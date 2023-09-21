# Logika Examples for A Formal Logic Introduction Course

This repository holds Logika examples suitable for an undergraduate 
formal logic introduction course (e.g., K-State's CIS 301: Logical
Foundations of Programming) that discusses:

* [Truth Table](src/truthtable)
* [Propositional Logic](src/propositional)
* [Predicate Logic](src/predicate)
* [Programming Logic](src/programming)
  * [Manual Verification](src/programming/manual)
  * [Automated Verification](src/programming/auto)

## Setup

1. Install [Sireum](https://sireum.org/getting-started/), and 
   set `SIREUM_HOME` environment variable to the Sireum directory.

2. Clone this repository to a `<PATH>`

3. Generate Sireum IVE project files:

   * **macOS/Linux**:

     ```sh
     $SIREUM_HOME/bin/sireum proyek ive <PATH>
     ```

   * **Windows**:

     ```cmd
     %SIREUM_HOME%\bin\sireum.bat proyek ive <PATH>
     ```

4. Open `<PATH>` in Sireum IVE

To verify all the examples using Sireum CLI:

* **macOS/Linux**:

  ```sh
  <PATH>/bin/verify.cmd
  ```

* **Windows**:

  ```cmd
  <PATH>\bin\verify.cmd
  ```
