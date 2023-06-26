#include <stdio.h>

struct node {
    int data;
    struct node *left;
    struct node *right;
};

struct node *insert_node(struct node *root, struct node *new_node, int data) {
    struct node *current;
    struct node *parent;
    int is_left_child;
    struct node *if_null;
    struct node *while_null;
    int curr_data;

    current = root;
    parent = NULL;
    is_left_child = 0;
    if_null = NULL;

    if (root == if_null) {
        return NULL;
    }

    while_null = NULL;
    while (current != while_null) {
        parent = current;
        curr_data = current->data;

        if (data > curr_data) {
            current = current->left;
            is_left_child = 1;
        } else {
            current = current->right;
            is_left_child = 0;
        }
    }
    while_null = NULL;

    if (is_left_child == 1) {
        parent->left = new_node;
    } else {
        parent->right = new_node;
    }

    return root;
}
