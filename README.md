
# Formal Verification Verifier

This project is a formal verification tool designed to prove the correctness of simple programs that use only integer variables, `while` loops, and `if-else` statements, and functions. The tool ensures small-scale program properties and behaviors meet specified expectations.

## Project Structure

- **Tokenization**: Uses `Parser.Tokenizer` to break down the input text.
- **Parsing**: Converts tokens into a structured format.
- **Execution (optional)**: Runs the code if the `-run` flag is set.
- **Verification**: Verifies the parsed code against formal rules. Verification has 3 stages:
    - *Preprocessing*: Replace function applications by inner variables, and add the logic that defines the functions (asseert the pre conditions, assume the post condition).
    - *Verfication Condition*: calculate the VC of the code.
    - *Z3 solver*: Check if the VC is valid (i.e., it's negation isn't satisfiable) using z3.

## 'While' Language Syntax

- **Assignment**:
```c
x := 0;
y := (x + y) * 5;
```
- **`if-else` statements**:
```c
if (condition) then {
    # code... ;
}
else{
    # code... ;
};
```
- **`while` loops**:
```c
while (condition){
# Invariant:
inv [logical_expression];
# code.... ;
};
```
- **assert/assume**:
```c
assume [logical_expression];
assert [logical_expression];
```
- **Functions**:
    - Returns one output, one single return at the end​ is allowed
    - No use of global variables​
    - Can not assign to input variables​
    - The only free variables in pre-conditions are the inputs​
    - The only free variables in post-conditions are the inputs + RET
```c
def func_name(x1,...,xn) {
  assume [pre_conditions(x1,...,xn)];
  #code....;
  return var;
  assert [post_cond(RET,x1,...,xn)]; // e.g.: assert RET > 0 ;
};
```
- **supported expression**:
    - **Arithmetic symbols**:
        - **Infix:**  +, -, /, % (The standard semantic...)
        - **Prefix:**  +, - (e.g: -1, +3)
    - **conditional symbols**:
        - **Infix:**  >, <, >=, <=, =, !=, && (AND), || (OR), -> (implies), <-> (iff)
        - **Prefix:**  ! (not)
    - **comments**: # (one line comment),  /* (multi-line comment) */

- **Logical function**: function which are used in verifications properties that were not defined will be considered as Z3_function, can be used for proof.
    - logical functions are not very useful without a "defintion". This is where the forall command comes in.
    - assumtion for a forall syntax:
        - should be wrriten only on the outer block, assumption will be applied in all code's blocks.
        - Should not include free-varibles (which are not mentioned in the begining of statment).
        - Z3 will probably get better results for bounded model checking.
    - assumtion for a logical function syntax:
```c
forall x1,x2,...,xk :: [logical expression];
# for example:
forall x1,x2,...,xk :: F(x1) > 0 && ((x3 !=0) -> G(x2,x3) > 0);
# Bounded Model Checking:
forall x :: ((x < 20 && 0 < x) -> FACT(x) = x * FACT(x-1)) && (FACT(0) = 1);
```
## Usage
1. **Install Z3 solver Package (if needed)**:
   ```bash
   pip install z3-solver
   ```
2. **Clone the repository**:
```bash
git clone https://github.com/YuvalLot/FormalVerificationProject.git
   ```
3. **Run the Verifier**:
   - Default verification file: `file1.while`
   - Or specify a file to verify:
     ```bash
     python main.py <filename> [-pre, -VC, -inner, -weak_post, -run]
     ```
   - Use **flags** for specific modes:
       - `-run`: execute the 'while' code (in partiular, don't verify it).
       - `-pre`: print the Preprocessor results.
       - `-VC`: print the Verfication Condition set before trying to prove/unprove correctness.
       - `-inner`: Shows assignments of temp varible on couner examples (temp varible were defined by the prover and not by the user).
       - `-weak_post`: Use weak post conditions (i.e., remove the addition of the origin of inner variables that replace function uses). This is useful for tidying of the counter-examples as it removes the function interpertation z3 adds. 
       - `-annot`: print the original code with line by line calculations of the wlp (if multiple conditions exist, they are separated by semi-colons).
       
## Dependencies
- Python 3.x
- Z3 4.13.0.0

## Example

Save this sample program in a file (e.g., `sample_program.while`):

```c
x := 0;
while (x < 5) {
    inv x >= 0 && x < 6;
    x := x + 1;
}
assert(x = 5);
```

Then, run the verifier as follows:

```bash
python main.py tests/sample_program.while
```

The verifier will check the program's assertions and output the results.


