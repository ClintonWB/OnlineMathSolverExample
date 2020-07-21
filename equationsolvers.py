#!/usr/bin/env python3
from sympy import Eq, latex
import sympy

from sympy.parsing.sympy_parser import (parse_expr, convert_equals_signs,
    implicit_multiplication, standard_transformations)
from textwrap import dedent

# Linear Equation Solver
def linear_solver(sub):
    r"""Linear Equation Checker/Solver.

    Checks whether a given string is a linear equation in one variable,
    and if so, returns an explanation of how to solve it.

    Parameters
    ----------

    sub : str
        The submitted expression, as a math string, to be passed to SymPy.

    Returns
    -------

    explanation:
        False if unable to parse as linear,
        A worked thorugh $\LaTeX$ explanation otherwise.

    Examples
    --------

    >>> linear_solver("")
    False

    >>> linear_solver("something abstract")
    False

    >>> linear_solver("x+1")
    False

    >>> linear_solver("x**2+1=1")
    False

    >>> print(linear_solver("x=1"))
    Let's solve the equation:
    \[
        x = 1
    \]
    The equation is in the form $x = 1$;
    That is, the value of $x$ is $1$.

    >>> print(linear_solver("x=0"))
    Let's solve the equation:
    \[
        x = 0
    \]
    The equation is in the form $x = 0$;
    That is, the value of $x$ is $0$.

    >>> print(linear_solver("a-1=1"))
    Let's solve the equation:
    \[
        a - 1 = 1
    \]
    First, we subtract -1 from both sides:
    \begin{align*}
        (a - 1)-(-1) &= 1-(-1) \\
        a &= 2
    \end{align*}
    The equation is in the form $a = 2$;
    That is, the value of $a$ is $2$.

    >>> print(linear_solver("5/3y=2"))
    Let's solve the equation:
    \[
        \frac{5 y}{3} = 2
    \]
    We have just one term on the left:
    The variable $y$ with coefficient $\frac{5}{3}$.
    Divide both sides by $\frac{5}{3}$:
    \begin{align*}
        \frac{ \frac{5 y}{3} }{ \frac{5}{3} } &=
        \frac{ 2 }{ \frac{5}{3} } \\
        y &= \frac{6}{5}
    \end{align*}
    The equation is in the form $y = \frac{6}{5}$;
    That is, the value of $y$ is $\frac{6}{5}$.

    >>> print(linear_solver("3a-1=1"))
    Let's solve the equation:
    \[
        3 a - 1 = 1
    \]
    First, we subtract -1 from both sides:
    \begin{align*}
        (3 a - 1)-(-1) &= 1-(-1) \\
        3 a &= 2
    \end{align*}
    We have just one term on the left:
    The variable $a$ with coefficient $3$.
    Divide both sides by $3$:
    \begin{align*}
        \frac{ 3 a }{ 3 } &=
        \frac{ 2 }{ 3 } \\
        a &= \frac{2}{3}
    \end{align*}
    The equation is in the form $a = \frac{2}{3}$;
    That is, the value of $a$ is $\frac{2}{3}$.

    >>> print(linear_solver("a-1=1"))
    Let's solve the equation:
    \[
        a - 1 = 1
    \]
    First, we subtract -1 from both sides:
    \begin{align*}
        (a - 1)-(-1) &= 1-(-1) \\
        a &= 2
    \end{align*}
    The equation is in the form $a = 2$;
    That is, the value of $a$ is $2$.
    """
    # Check if SymPy can parse the expression as an equation
    try:
        expr = parse_expr(sub,
                   transformations=(*standard_transformations,
                                    implicit_multiplication,
                                    convert_equals_signs))
    except (SyntaxError, ValueError):
        return False

    # Verify the structure of the equation

    # Check if the expression is in 1 variable
    variables = expr.free_symbols
    if len(variables) != 1:
        return False
    x, = variables

    # Check if it is a linear equation
    if not isinstance(expr, Eq):
        return False
    if not expr.rhs.is_constant():
        return False
    if not expr.lhs.diff(x).is_constant():
        return False

    # Now that we know the structure of the equation,
    # we can turn it into a worked-through solution.

    explanation = dedent("""\
    Let's solve the equation:
    \\[
        {expression}
    \\]
    """.format(expression=latex(expr)))
    lhs = expr.lhs
    rhs = expr.rhs
    coeff = lhs.coeff(x)
    left_constant = lhs - coeff*x

    # Use conditional blocks to construct content that only sometimes shows up.
    if not left_constant.is_zero:
        new_rhs = rhs - left_constant
        new_lhs = lhs - left_constant
        explanation += dedent("""\
        First, we subtract {left_constant} from both sides:
        \\begin{{align*}}
            ({old_lhs})-({left_constant}) &= {old_rhs}-({left_constant}) \\\\
            {new_lhs} &= {new_rhs}
        \\end{{align*}}
        """.format(left_constant = left_constant,
                   old_lhs = latex(lhs),
                   old_rhs = latex(rhs),
                   new_lhs = latex(new_lhs),
                   new_rhs = latex(new_rhs),
                   ))
        lhs = new_lhs
        rhs = new_rhs

    if not coeff == 1:
        new_rhs = rhs/coeff
        new_lhs = lhs/coeff
        explanation += dedent("""\
        We have just one term on the left:
        The variable ${variable}$ with coefficient ${coefficient}$.
        Divide both sides by ${coefficient}$:
        \\begin{{align*}}
            \\frac{{ {old_lhs} }}{{ {coefficient} }} &=
            \\frac{{ {old_rhs} }}{{ {coefficient} }} \\\\
            {new_lhs} &= {new_rhs}
        \\end{{align*}}
        """.format(coefficient = latex(coeff),
                   variable = latex(x),
                   old_lhs = latex(lhs),
                   old_rhs = latex(rhs),
                   new_lhs = latex(new_lhs),
                   new_rhs = latex(new_rhs),
                   ))
        lhs = new_lhs
        rhs = new_rhs

    explanation += dedent("""\
        The equation is in the form ${variable} = {value}$;
        That is, the value of ${variable}$ is ${value}$.""".format(
        variable = latex(x),
        value = latex(rhs)))

    return explanation


# Exponential
# Examples:
#     "e^x-5=2"
#     "1+2e^(x-1)=5"
#     "1-2e^(x-1)=5"
def exponential_solver(sub):
    return False


# Logarithm
# Examples:
#     "ln(x)=3"
#     "ln(2x)-1=4"
#     "ln(3x)+3=2"
#     "ln(3a+1)-1=3"
# As a challenge,
# You can also choose to support other formats of log
def logarithm_solver(sub):
    return False


# Square Roots
# Examples:
#     "sqrt(x+1)=2"
#     "2sqrt(2x-3)+3=5"
#     "1-2sqrt(2-x)=3"
# As a challenge, you can consider other roots like ^(1/3).
def square_root_solver(sub):
    try:
        expr = parse_expr(sub,
                   transformations=(*standard_transformations,
                                    implicit_multiplication,
                                    convert_equals_signs))
    except (SyntaxError, ValueError):
        return False

    # Verify the structure of the equation

    # Check if the expression is in 1 variable
    variables = expr.free_symbols
    if len(variables) != 1:
        return False
    x, = variables

    # Check if it is a linear equation
    if not isinstance(expr, Eq):
        return False
    if not expr.rhs.is_constant():
        return False
    try:
        sqrinsm = 1/(expr.lhs.diff(x)**2)
    except:
        return False
    if not sqrinsm.diff(x).is_constant():
        return False
    # Now that we know the structure of the equation,
    # we can turn it into a worked-through solution.

    explanation = dedent("""\
    Let's solve the equation:
    \\[
        {expression}
    \\]
    """.format(expression=latex(expr)))
    lhs = expr.lhs
    rhs = expr.rhs
    #coeff = lhs.coeff(x)
    left_constant = sympy.simplify(lhs - sympy.integrate(lhs.diff(x),x))
    # Use conditional blocks to construct content that only sometimes shows up.
    if not left_constant.is_zero:
        new_rhs = rhs - left_constant
        new_lhs = lhs - left_constant
        explanation += dedent("""\
        First, we subtract {left_constant} from both sides:
        \\begin{{align*}}
            ({old_lhs})-({left_constant}) &= {old_rhs}-({left_constant}) \\\\
            {new_lhs} &= {new_rhs}
        \\end{{align*}}
        """.format(left_constant = left_constant,
                   old_lhs = latex(lhs),
                   old_rhs = latex(rhs),
                   new_lhs = latex(new_lhs),
                   new_rhs = latex(new_rhs),
                   ))
        lhs = new_lhs
        rhs = new_rhs
    new_rhs = rhs**2
    new_lhs = lhs**2
    explanation += dedent("""\
        Now, we square both sides to get rid of the square root.
        \\begin{{align*}}
            ({old_lhs})^2 &= ({old_rhs})^2 \\\\
            {new_lhs} &= {new_rhs}
        \\end{{align*}}
        """.format(old_lhs = latex(lhs),
                   old_rhs = latex(rhs),
                   new_lhs = latex(new_lhs),
                   new_rhs = latex(new_rhs),
                   ))

    rhs = new_rhs
    lhs = new_lhs
    coeff = lhs.coeff(x)
    left_constant = sympy.simplify(lhs - sympy.integrate(lhs.diff(x),x))
    # Use conditional blocks to construct content that only sometimes shows up.
    if not left_constant.is_zero:
        new_rhs = rhs - left_constant
        new_lhs = lhs - left_constant
        explanation += dedent("""\
        Next, we subtract {left_constant} from both sides:
        \\begin{{align*}}
            ({old_lhs})-({left_constant}) &= {old_rhs}-({left_constant}) \\\\
            {new_lhs} &= {new_rhs}
        \\end{{align*}}
        """.format(left_constant = left_constant,
                   old_lhs = latex(lhs),
                   old_rhs = latex(rhs),
                   new_lhs = latex(new_lhs),
                   new_rhs = latex(new_rhs),
                   ))
        lhs = new_lhs
        rhs = new_rhs
    if not coeff == 1:
        new_rhs = rhs/coeff
        new_lhs = lhs/coeff
        explanation += dedent("""\
        We have just one term on the left:
        The variable ${variable}$ with coefficient ${coefficient}$.
        Divide both sides by ${coefficient}$:
        \\begin{{align*}}
            \\frac{{ {old_lhs} }}{{ {coefficient} }} &=
            \\frac{{ {old_rhs} }}{{ {coefficient} }} \\\\
            {new_lhs} &= {new_rhs}
        \\end{{align*}}
        """.format(coefficient = latex(coeff),
                   variable = latex(x),
                   old_lhs = latex(lhs),
                   old_rhs = latex(rhs),
                   new_lhs = latex(new_lhs),
                   new_rhs = latex(new_rhs),
                   ))
        lhs = new_lhs
        rhs = new_rhs
    explanation += dedent("""\
        The equation is in the form ${variable} = {value}$;
        That is, the value of ${variable}$ is ${value}$.""".format(
        variable = latex(x),
        value = latex(rhs)))

    return explanation

# Quadratic Equation Solver
# Examples:
#    "x**2+2x+1=0"
#    "y**2+1=0"
#    "z**2+3z+2=0"
def quadratic_solver(sub):
    r"""Quadratic Equation Checker/Solver.

    Checks whether a given string is a linear equation in one variable,
    and if so, returns an explanation of how to solve it.

    Parameters
    ----------

    sub : str
        The submitted expression, as a math string, to be passed to SymPy.

    Returns
    -------

    explanation:
        False if unable to parse as linear,
        A worked thorugh $\LaTeX$ explanation otherwise.

    Examples
    --------

    >>> quadratic_solver("")
    False

    >>> quadratic_solver("something abstract")
    False

    >>> quadratic_solver("x+1")
    False

    >>> print(quadratic_solver("x**2+1=1"))
    Let's solve the equation:
    \[
        x^{2} + 1 = 1
    \]
    Move the constant term to the right-hand side by subtraction:
    \begin{align*}
        x^{2} &= 0
    \end{align*}
    We are done; the only possible solution is $x = 0$.
    
    >>> print(quadratic_solver("x**2+2x+1=0"))
    Let's solve the equation:
    \[
        x^{2} + 2 x + 1 = 0
    \]
    Move the constant term to the right-hand side by subtraction:
    \begin{align*}
        x^{2} + 2 x &= -1
    \end{align*}
    Complete the square by adding $\left(2/2\right)^2$ to both sides:
    \begin{align*}
        x^{2} + 2 x + 1 &= 0
    \end{align*}
    and then factor:
    \begin{align*}
        \left(x + 1\right)^{2} &= 0
    \end{align*}
    Since the right-hand side is zero, there is only one way this can happen, specifically $x + 1 = 0$ or rather, $x = -1$.
    
    >>> print(quadratic_solver("y**2+1=0"))
    Let's solve the equation:
    \[
        y^{2} + 1 = 0
    \]
    Move the constant term to the right-hand side by subtraction:
    \begin{align*}
        y^{2} &= -1
    \end{align*}
    Take the positive and negative square-roots to find
    \begin{align*}
        y &= \pm i
    \end{align*}
    
    >>> print(quadratic_solver("z**2+3z+2=0"))
    Let's solve the equation:
    \[
        z^{2} + 3 z + 2 = 0
    \]
    Move the constant term to the right-hand side by subtraction:
    \begin{align*}
        z^{2} + 3 z &= -2
    \end{align*}
    Complete the square by adding $\left(3/2\right)^2$ to both sides:
    \begin{align*}
        z^{2} + 3 z + \frac{9}{4} &= \frac{1}{4}
    \end{align*}
    and then factor:
    \begin{align*}
        \left(z + \frac{3}{2}\right)^{2} &= \frac{1}{4}
    \end{align*}
    and take the positive and negative square roots:
    \begin{align*}
        z + \frac{3}{2} &= \pm \frac{1}{2}
    \end{align*}
    and finally, move the term $\frac{3}{2}$ to the other side, flipping its sign:
    \begin{align*}
        z &= - \frac{3}{2}\pm \frac{1}{2}
    \end{align*}
    That is a good answer, but we would do well to simplify when we can:
    \begin{align*}
        z &= -1 &\text{or} z &= -2
    \end{align*}
    """
    # Check if SymPy can parse the expression as an equation
    try:
        expr = parse_expr(sub,
                   transformations=(*standard_transformations,
                                    implicit_multiplication,
                                    convert_equals_signs))
    except (SyntaxError, ValueError):
        return False
    
    # Verify the structure of the equation

    # Check if the expression is in 1 variable
    variables = expr.free_symbols
    if len(variables) != 1:
        return False
    x, = variables
    
    # Check if it is a quadratic equation
    if not isinstance(expr, Eq):
        return False
    if not expr.rhs.is_constant():
        return False
    if expr.lhs.diff(x).is_constant():
        return False
    if not expr.lhs.diff(x, 2).is_constant():
        return False
    
    # Now that we know the structure of the equation,
    # we can turn it into a worked-through solution.

    explanation = dedent("""\
        Let's solve the equation:
        \\[
            {expression}
        \\]
    """.format(expression=latex(expr)))
    lhs = expr.lhs
    rhs = expr.rhs
    a = lhs.coeff(x, 2)
    b = lhs.coeff(x, 1)
    c = lhs.coeff(x, 0)
    
    if c != 0:
        mode = "subtraction" if c>0 else "addition"
        rhs = rhs-c
        explanation += dedent("""\
            Move the constant term to the right-hand side by {}:
            \\begin{{align*}}
                {} &= {}
            \\end{{align*}}
        """.format(
            mode,
            latex(a*x**2+b*x),
            latex(rhs),
        ))
    
    if a != 1:
        b /= a
        rhs /= a
        explanation += dedent("""\
            Divide through by the coefficient of ${}^2$:
            \\begin{{align*}}
                {} &= {}
            \\end{{align*}}
        """.format(
            x,
            latex(x**2+b*x),
            latex(rhs),
        ))
    
    if rhs==0:
        explanation += dedent("""\
            We are done; the only possible solution is ${} = 0$.""".format(
            latex(x)
        ))
        return explanation
    
    if b==0:
        explanation += dedent("""\
            Take the positive and negative square-roots to find
            \\begin{{align*}}
                {} &= \\pm {}
            \\end{{align*}}""".format(
            latex(x),
            latex(sympy.sqrt(rhs))
        ))
        return explanation
    
    rhs += (b/2)**2
    explanation += dedent("""\
        Complete the square by adding $\\left({}/2\\right)^2$ to both sides:
        \\begin{{align*}}
            {} &= {}
        \\end{{align*}}
    """.format(
        latex(b),
        latex(x**2+b*x+(b/2)**2),
        latex(rhs)
    ))
    explanation += dedent("""\
        and then factor:
        \\begin{{align*}}
            {} &= {}
        \\end{{align*}}
    """.format(
        latex((x+b/2)**2),
        latex(rhs)
    ))
    
    if rhs==0:
        explanation += dedent("""\
            Since the right-hand side is zero, there is only one way this can happen, specifically ${} = 0$ or rather, ${} = {}$.""".format(
            latex(x+b/2),
            latex(x),
            latex(-b/2)
        ))
        return explanation
    
    
    explanation += dedent("""\
        and take the positive and negative square roots:
        \\begin{{align*}}
            {} &= \\pm {}
        \\end{{align*}}
    """.format(
        latex(x+b/2),
        latex(sympy.sqrt(rhs))
    ))
    explanation += dedent("""\
        and finally, move the term ${}$ to the other side, flipping its sign:
        \\begin{{align*}}
            {} &= {}\\pm {}
        \\end{{align*}}
    """.format(
        latex(b/2),
        latex(x),
        latex(-b/2),
        latex(sympy.sqrt(rhs)),
    ))
    simplified1 = sympy.simplify(-b/2+sympy.sqrt(rhs))
    simplified2 = sympy.simplify(-b/2-sympy.sqrt(rhs))
    explanation += dedent("""\
        That is a good answer, but we would do well to simplify when we can:
        \\begin{{align*}}
            {} &= {} &\\text{{or}} {} &= {}
        \\end{{align*}}""".format(
        latex(x),
        simplified1,
        latex(x),
        simplified2
    ))
    
    return explanation


# Systems of Linear Equations Solver
# Examples:
#     "a+2b = 1,a-b=3"
#     "3x+2/3y=5/2,5x-y=2"
# You can do it in only two dimensions if you want,
# or challenge yourself to do it for more.
def system_of_linear_equations_solver(sub):
    return False


# Export solvers as a list
equation_solvers = (linear_solver,
                    quadratic_solver,
                    logarithm_solver,
                    exponential_solver,
                    square_root_solver,
                    system_of_linear_equations_solver,
                    )


if __name__ == "__main__":
    import doctest
    doctest.testmod()
