#include <stdio.h>

#define BLACK 0;
#define RED 1;

struct node {
    int data;
    int color;
    struct node *left;
    struct node *right;
    struct node *parent;
};

void insert_node(struct node **root, struct node *new_node, int data) {
    struct node *current;
    struct node *parent;
    struct node *if_null;
    struct node *while_null;
    int curr_data;

    current = *root;
    parent = NULL;
    if_null = NULL;

    if (*root == if_null) {
        *root = new_node;
        new_node->color = BLACK;
        return;
    }

    while_null = NULL;

    while (current != while_null) {
        parent = current;
        curr_data = parent->data;

        if (data < curr_data) {
            current = current->left;
        } else {
            current = current->right;
        }
    }

    while_null = NULL;

    return;
}
