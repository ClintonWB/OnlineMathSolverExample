#!/usr/bin/env python3
from sympy import Eq, latex

from sympy.parsing.sympy_parser import (parse_expr, convert_equals_signs,
    implicit_multiplication, standard_transformations)
from textwrap import dedent

def linear_logic(expr,x):
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

    return explanation,rhs

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
    except:
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
    return linear_logic(expr,x)[0]

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
    return False


# Quadratic Equation Solver
# Examples:
#    "x**2+2x+1=0"
#    "y**2+1=0"
#    "z**2+3z+2=0"
def quadratic_solver(sub):
    return False


# Systems of Linear Equations Solver
# Examples:
#     "a+2b = 1,a-b=3"
#     "3x+2/3y=5/2,5x-y=2"
# You can do it in only two dimensions if you want,
# or challenge yourself to do it for more.
def system_of_linear_equations_solver(sub):
    #separate the equations at the comma
    eqns=sub.split(",")
    if len(eqns) != 2:
        return False
    # Check if SymPy can parse the expressions as equations
    try:
        expr=[]
        for i in eqns:
            expr.append(parse_expr(i,
                   transformations=(*standard_transformations,
                                    implicit_multiplication,
                                    convert_equals_signs)))
    except:
        return False

    # Verify the structure of the equations

    # Check if the expressions are in 2 variables
    variables=set()
    for i in expr:
        variables.update(i.free_symbols)
        if len(i.free_symbols) != 2:
            return False
    if len(variables) != 2:
        return False
    x,y, = variables

    # Check if they are linear equations
    for i in expr:
        if not isinstance(i, Eq):
            return False
        if not i.rhs.is_constant():
            return False
        if not i.lhs.diff(x).is_constant():
            return False
        if not i.lhs.diff(y).is_constant():
            return False

    # Now that we know the structure of the equations,
    # we can turn them into a worked-through solution.

    lhs=[]
    rhs=[]
    coeff=[]
    for i in expr:
        lhs.append(i.lhs)
        rhs.append(i.rhs)
        coeff.append((lhs[-1].coeff(x),lhs[-1].coeff(y)))

    explanation = dedent("""\
    Let's solve the system of equations:
    \\[
        \\begin{{align*}}
            {left1}&={right1}\\\\
            {left2}&={right2}
        \\end{{align*}}
    \\]
    """.format(left1=latex(lhs[0]),left2=latex(lhs[1]),
               right1=latex(rhs[0]),right2=latex(rhs[1])))

    new_coeff=[1]
    new_coeff.extend(new_coeff[-1]*i[0] for i in coeff)
    new_coeff=new_coeff[-1]
    new_lhs=[lhs[i]*new_coeff/coeff[i][0] for i in range(len(coeff))]
    new_rhs=[rhs[i]*new_coeff/coeff[i][0] for i in range(len(coeff))]

    if any(i[0]!=coeff[0][0] for i in coeff):
        explanation+=dedent("""\
        First we multiply each equation by the coefficient of ${variable}$ in the other equations.
        This way they will all have the same coefficient for ${variable}$.
        """.format(variable=latex(x)))

        if coeff[1][0]!=1:
            explanation+=dedent("""\
            \\begin{{align*}}
                {coeff1}\\left({left1}\\right)&={coeff1}\\left({right1}\\right)\\\\
                {new_left1}&={new_right1}
            \\end{{align*}}
            """.format(variable=latex(x),coeff1=latex(new_coeff/coeff[0][0]),
                       left1=latex(lhs[0]),new_left1=latex(new_lhs[0]),
                       right1=latex(rhs[0]),new_right1=latex(new_rhs[0])))

        if coeff[0][0]!=1:
            explanation+=dedent("""\
            \\begin{{align*}}
                {coeff2}\\left({left2}\\right)&={coeff2}\\left({right2}\\right)\\\\
                {new_left2}&={new_right2}
            \\end{{align*}}
            """.format(variable=latex(x),coeff2=latex(new_coeff/coeff[1][0]),
                       left2=latex(lhs[1]),new_left2=latex(new_lhs[1]),
                       right2=latex(rhs[1]),new_right2=latex(new_rhs[1])))

    combined_lhs=new_lhs[0]-new_lhs[1]
    combined_rhs=new_rhs[0]-new_rhs[1]

    explanation+=dedent("""\
    If we subtract the second equation from the first, we get:
    \\begin{{align*}}
        {left}&={right}
    \\end{{align*}}
    """.format(left=latex(combined_lhs),right=latex(combined_rhs)))

    if combined_lhs.is_constant():
        if (combined_lhs-combined_rhs).is_zero:
            explanation+=dedent("""\
            In this case, both variables ended up cancelling out since the two
            equations were scalar multiples of each other. Thus there are an
            infinite number of solutions to this system of equations.
            """)
        else:
            explanation+=dedent("""\
            But these values aren't equal, so there are no solutions to this system of equations.
            """)
        return explanation

    y_explanation,y_value=linear_logic(Eq(combined_lhs,combined_rhs),y)
    x_explanation,x_value=zip(*[linear_logic(i.subs(y,y_value),x) for i in expr])

    explanation+=dedent("""\
    Since this is now an equation in one variable, we can solve it like we would
    any other linear equation.
    \\begin{{align*}}
    \\end{{align*}}
    """.format())
    explanation+=y_explanation
    explanation+=dedent("""\
    \\begin{{align*}}
    \\end{{align*}}
    Plugging in ${value}$ for ${variable}$ in the first equation, we can now
    solve for ${other}$ like we would any other linear equation.
    \\begin{{align*}}
    \\end{{align*}}
    """.format(value=latex(y_value),variable=latex(y),other=latex(x)))
    explanation+=x_explanation[0]
    explanation+=dedent("""\
    \\begin{{align*}}
    \\end{{align*}}
    Thus we have found the pair of values which satisfy the two linear equations:
    ${var1}={val1}$ and ${var2}={val2}$.
    """.format(var1=latex(x),var2=latex(y),val1=latex(x_value[0]),val2=latex(y_value)))

    assert all(i==x_value[0] for i in x_value),"Deduced value for {x} should be equal for all expressions".format(x=x)
    return explanation

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
