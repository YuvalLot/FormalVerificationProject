
# Formal Verification Verifier

This project is a formal verification tool designed to prove the correctness of simple programs that use only integer variables, `while` loops, and `if-else` statements, and functions. The tool ensures small-scale program properties and behaviors meet specified expectations.

## Project Structure

- **Tokenization**: Uses `Parser.Tokenizer` to break down the input text.
- **Parsing**: Converts tokens into a structured format.
- **Execution (optional)**: Runs the code if the `-run` flag is set.
- **Verification**: Verifies the parsed code against formal rules.

## 'While' Language Syntax

- **assignment**:
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
# Inveriant:
inv [logical_expression];
# code.... ;
};
```
- **assert/assume**:
```c
assume [logical_expression];
assert [logical_expression];
```
- **functions**:
```c
def func_name(x1,...,xn) {
  assume [pre_conditions(x1,...,xn)];
  #code....;
  return var;
  assert [post_cond(RET,x1,...,xn)]; // e.g.: assert RET > 0 ;
};
```
- **suported expression**:
    - **Arithmetic symbols**:
        - **Infix:**  +, -, /, % (The standart semantic...)
        - **Prefix:**  +, - (e.g: -1, +3)
    - **conditional symbols**:
        - **Infix:**  >, <, >=, <=, =, !=, && (AND), || (OR), -> (implies), <-> (iff)
        - **Prefix:**  ! (not)
    - **coments**: # (one line comment)

- **Logical function**: function which are used in verfications properties that were not defined will be considered as Z3_function, can be used for prof.
    - assumtion for a logical function syntaxt:
```c
forall x:: [logical expression]
# for example:
forall x:: F(x) > 0
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
       - `-run`: execute the 'while' code.
       - `-pre`: print the Preprocessor results.
       - `-VC`: print the Verfication Condition set before trying to prove/unprove correctness.
       - `-inner`: Shows assignments of temp varible on couner examples (temp varible weredefined by the prover and not by the user).
       - `-weak_post`:Use weak post conditions (i.e., remove the addition of the origin of inner variables that replace function uses).
       
## Dependencies
- Python 3.x
- Z3 4.13.0.0

## Example

Save this sample program in a file (e.g., `sample_program.while`):

```c
x := 0;
while (x < 5) {
    x := x + 1;
}
assert(x = 5);
```

Then, run the verifier as follows:

```bash
python main.py tests/sample_program.while
```

The verifier will check the program's assertions and output the results.


