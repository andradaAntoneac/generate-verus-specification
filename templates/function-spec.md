# Function Spec Template

\`\`\`rust
fn FUNCTION_NAME(PARAMS) -> (RETURN_NAME: RETURN_TYPE)
    requires
        // preconditions from abstract spec
    ensures
        // postconditions; must use `final()` and `old()`  for the mutable parameters 
    // implementation
}
\`\`\`