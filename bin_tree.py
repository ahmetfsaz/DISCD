"""
Binary-tree utilities for tracking sentence combinations during model counting.

Nothing in this module is imported by name anywhere in the repository — every
script pulls it in with `from bin_tree import *` and calls none of its
functions. It looks like scaffolding from an earlier approach to selecting
which sentences overlap, superseded by the DIMACS/model-counting pipeline in
fol_parser.py. Recommended action: delete this file and drop the `bin_tree`
import from ICMLCN.py and WCNC.py. This cleaned version is kept only in case
something outside this repo still depends on it; if not, remove it.
"""

class Node:
    """A node in the tree, holding which sentence combination it represents."""

    def __init__(self, depth, id, parent=None):
        self.left = None
        self.right = None
        self.parent = parent
        self.depth = depth
        self.id = id


def find_first_overlap(large_list, small_list):
    """Return the first sublist of `large_list` whose prefix contains `small_list`.

    Compares every position of `small_list` against every contiguous window of
    each sublist's prefix (all but its last element), and returns the first
    sublist where a window matches.
    """
    small_len = len(small_list)

    for sublist in large_list:
        prefix = sublist[:-1]
        for i in range(len(prefix) - small_len + 1):
            if prefix[i : i + small_len] == small_list:
                return sublist

    return None


def insert_at_last_level(root, id, assignment, truth_table, keys, depth):
    """Insert a new node at the bottom of the tree, then prune by `truth_table`."""
    insert_at_level(root, depth, depth, id, assignment, truth_table, keys)


def insert_at_level(root, level, depth, id, assignment, truth_table, keys):
    """Recurse to `level`, add a node there, and mark branches ruled out by `truth_table`.

    `assignment` maps node ids to a boolean path so far. At the target level, a
    new left and right child are added for `id`; each is then checked against
    `truth_table` under the combined assignment, and pruned (set to `False`)
    if that combination cannot occur.
    """
    if level == 1:
        if root is False:
            return

        if root.left is not False:
            root.left = Node(depth, id, root)
            for root_val, id_val, branch in (
                (False, False, "left"),
                (False, True, "right"),
            ):
                assignment[root.id], assignment[id] = root_val, id_val
                values = [assignment[key] for key in keys if key in assignment]
                result = find_first_overlap(truth_table, values)
                if result is not None and result[-1] is False:
                    setattr(root.left, branch, False)

        if root.right is not False:
            root.right = Node(depth, id, root)
            for root_val, id_val, branch in (
                (True, False, "left"),
                (True, True, "right"),
            ):
                assignment[root.id], assignment[id] = root_val, id_val
                values = [assignment[key] for key in keys if key in assignment]
                result = find_first_overlap(truth_table, values)
                if result is not None and result[-1] is False:
                    setattr(root.right, branch, False)

    elif level > 1:
        if root is False:
            return
        if root.left is not None:
            assignment[root.id] = False
            insert_at_level(root.left, level - 1, depth, id, assignment, truth_table, keys)
        if root.right is not None:
            assignment[root.id] = True
            insert_at_level(root.right, level - 1, depth, id, assignment, truth_table, keys)


def delete_at_level(root, level, var_levels, path, current_level):
    """Prune the subtree at `level`, following `path` at each level in `var_levels`.

    At levels not in `var_levels` both children are visited; at a level in
    `var_levels`, only the branch `path` selects is visited.
    """
    if level == 1:
        root.left = None
        root.right = None
        return

    if level <= 1:
        return

    if current_level in var_levels:
        index = var_levels.index(current_level)
        if root.left is not None and path[index] == 0:
            delete_at_level(root.left, level - 1, var_levels, path, current_level + 1)
        if root.right is not None and path[index] == 1:
            delete_at_level(root.right, level - 1, var_levels, path, current_level + 1)
    else:
        if root.left is not None:
            delete_at_level(root.left, level - 1, var_levels, path, current_level + 1)
        if root.right is not None:
            delete_at_level(root.right, level - 1, var_levels, path, current_level + 1)


def eliminate_at_given_level(root, id, repeated, path, variables):
    """Prune the subtree below `id`, following `path` at each variable's level."""
    level = repeated.index(id)
    var_levels = [repeated.index(v) for v in variables]
    delete_at_level(root, level, var_levels, path, current_level=1)


def height(node):
    """Height of the tree: the number of nodes on its longest root-to-leaf path."""
    if node is None:
        return 0

    left_height = 1 if node.left is False else height(node.left)
    right_height = 1 if node.right is False else height(node.right)
    return max(left_height, right_height) + 1


def print_inorder(root):
    if root:
        print_inorder(root.left)
        print(root.id, end=" ")
        print_inorder(root.right)


def print_preorder(root):
    if root:
        print(root.id, end=" ")
        print_preorder(root.left)
        print_preorder(root.right)


def print_postorder(root):
    if root:
        print_postorder(root.left)
        print_postorder(root.right)
        print(root.id, end=" ")


def print_level_order(root, num_levels):
    """Print node ids level by level, from the root down to `num_levels`."""
    for level in range(1, num_levels + 1):
        print_level_at(root, level)


def print_level_at(root, level):
    if root is None or root is False:
        return
    if level == 1:
        print(root.id, end=" ")
    elif level > 1:
        print_level_at(root.left, level - 1)
        print_level_at(root.right, level - 1)


def flip_majority_truth_value(truth_tables):
    """Flip every truth value if True outnumbers False across all tables.

    Balances a set of truth tables toward an equal split of True and False
    outcomes, which model counting treats symmetrically either way.
    """
    def count_true_false(tables):
        true_count = false_count = 0
        for table in tables:
            for row in table:
                if row[-1] is True:
                    true_count += 1
                else:
                    false_count += 1
        return true_count, false_count

    true_count, false_count = count_true_false(truth_tables)
    if false_count and true_count / false_count > 1:
        for table in truth_tables:
            for row in table:
                row[-1] = not row[-1]

    return truth_tables
