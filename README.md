
# Formal Verification Verifier

This project is a formal verification tool designed to prove the correctness of simple programs that use only integer variables, `while` loops, and `if-else` statements. The tool ensures small-scale program properties and behaviors meet specified expectations.

## Features

- **Minimal syntax support**: Handles `int` data types, `while` loops, `if-else` statements, and simple\raw functions.
- **Formal verification**: Proves properties for simple programs or identifies counterexamples.
- **Focused analysis**: Designed for efficiency in verifying minimalistic program structures.

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
  assert [post_cond(RET)]; // e.g.: assert RET > 0 ;
};
```

## Project Structure

- **src/**: Contains the main source code for the verifier.
- **tests/**: Holds test cases for sample programs, helping validate the tool’s accuracy.
- **docs/**: Contains documentation files and additional resources.

## Installation

Clone the repository and navigate to the project directory:

```bash
git clone https://github.com/YuvalLot/FormalVerificationProject.git
cd FormalVerificationProject
```

Ensure the required dependencies are installed:

```bash
# Example for Python projects
pip install -r requirements.txt
```

## Usage

To verify a program, run the main script located in the `src/` directory, specifying the path to the file you wish to verify:

```bash
python src/main.py path/to/your_program
```

### Example

Save this sample program in a file (e.g., `sample_program.c`):

```c
int x = 0;
while (x < 5) {
    x = x + 1;
}
assert(x == 5);
```

Then, run the verifier as follows:

```bash
python src/main.py tests/sample_program.c
```

The verifier will check the program's assertions and output the results.

## Contributing

Contributions are welcome! Please open an issue for any bugs or desired features, or submit a pull request.

## License

This project is licensed under the MIT License. See `LICENSE` for details.
