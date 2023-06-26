#include <stdio.h>

typedef struct node {
    int data;
    struct node *left;
    struct node *right;
} node;

node *search_node(node *root, int value) {
    node *current;
    node *temp_null;
    int temp_data;

    current = root;
    temp_null = NULL;

    while (current != temp_null) {
        temp_data = current->data;
        if (temp_data == value) {
            return current;
        }

        if (temp_data < value) {
            current = current->right;
        } else {
            current = current->left;
        }
    }

    temp_null = NULL;
    return NULL;
}
