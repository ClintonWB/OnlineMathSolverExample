#!/usr/bin/env python3
from sympy import Eq, latex
from sympy import exp

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
    r"""Logarithmic Equation Checker/Solver.

    Checks whether a given string is a logarithmic equation in one variable,
    and if so, returns an explanation of how to solve it.

    Parameters
    ----------

    sub : str
        The submitted expression, as a math string, to be passed to SymPy.

    Returns
    -------

    explanation:
        False if unable to parse as logarithmic,
        A worked thorugh $\LaTeX$ explanation otherwise.

    Examples
    --------

    >>> logarithm_solver("")
    False

    >>> logarithm_solver("something abstract")
    False

    >>> logarithm_solver("x+1")
    False

    >>> logarithm_solver("x**2+1=1")
    False

    >>> print(logarithm_solver("ln(2x)-1=4"))
    Let's solve the equation:
    \[
        \log{\left(2 x \right)} - 1 = 4
    \]
    First, we subtract -1 from both sides:
    \begin{align*}
        (\log{\left(2 x \right)} - 1)-(-1) &= 4-(-1) \\
        \log{\left(2 x \right)} &= 5
    \end{align*}
    Raise $e$ to both sides:
    \begin{align*}
        \ e^{old_lhs} &= e^{old_rhs} \\
        2 x &= e^{5}
    \end{align*}
    Let's solve the equation:
    \[
        2 x = e^{5}
    \]
    We have just one term on the left:
    The variable $x$ with coefficient $2$.
    Divide both sides by $2$:
    \begin{align*}
        \frac{ 2 x }{ 2 } &=
        \frac{ e^{5} }{ 2 } \\
        x &= \frac{e^{5}}{2}
    \end{align*}
    The equation is in the form $x = \frac{e^{5}}{2}$;
    That is, the value of $x$ is $\frac{e^{5}}{2}$.

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

    # Check if it is a logarithmic equation
    if not isinstance(expr, Eq):
        return False
    if not expr.rhs.is_constant():
        return False

    explanation = dedent("""\
    Let's solve the equation:
    \\[
        {expression}
    \\]
    """.format(expression=latex(expr)))
    lhs = expr.lhs
    rhs = expr.rhs
    left_constant = lhs.coeff(x,0)

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

    new_rhs = exp(rhs)
    new_lhs = exp(lhs)
    explanation += dedent("""\
    Raise $e$ to both sides:
    \\begin{{align*}}
        \\ e^{{old_lhs}} &= e^{{old_rhs}} \\\\
        {new_lhs} &= {new_rhs}
    \\end{{align*}}
    """.format(old_lhs = latex(lhs),
                  old_rhs = latex(rhs),
                  new_lhs = latex(new_lhs),
                  new_rhs = latex(new_rhs),
                  ))
    lhs = new_lhs
    rhs = new_rhs

    return explanation + linear_solver(str(lhs)+"="+str(rhs))


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

    # Check if it is a quadratic equation
    if not isinstance(expr, Eq):
        return False
    if not expr.rhs.is_zero:
        return False
    if expr.lhs.diff(x).is_constant():
        return False
    if not expr.lhs.diff(x).diff(x).is_constant():
        return False


    #convert the equation into varaibles.
    explanation = dedent("""\
    Let's solve the equation:
    \\[
        {expression}
    \\]
    """.format(expression=latex(expr)))
    lhs = expr.lhs
    rhs = expr.rhs
    coeff1 = lhs.coeff(x**2)
    coeff2 = lhs.coeff(x)
    constant = lhs -coeff2*x -coeff1*x**2

    # Aplly the quadratic formula
    explanation += "We apply the quadratic formula:"

    explanation += dedent("""\
    \\begin{{align*}}
        \\frac{{-({coeff2}) \pm \sqrt{{{coeff2}^2-4\cdot{coeff1}\cdot{constant}}}}}{{2\cdot{coeff1}}}
    \\end{{align*}}
    """.format(coeff1 = latex(coeff1),
                coeff2 = latex(coeff2),
                constant = latex(constant)))

    discriminant = coeff2**2-4*coeff1*constant
    denominator = 2*coeff1
    leader = -1*coeff2
    explanation += dedent("""We simplify:""")

    explanation += dedent("""\
    \\begin{{align*}}
        \\frac{{{leader} \pm \sqrt{{{discriminant}}}}}{{{denominator}}}
    \\end{{align*}}
    """.format(leader= latex(leader),
                discriminant = latex(discriminant),
                denominator = latex(denominator)
                ))


    return explanation
    return False


# Systems of Linear Equations Solver
# Examples:
#     "a+2b = 1,a-b=3"
#     "3x+2/3y=5/2,5x-y=2"
# You can do it in only two dimensions if you want,
# or challenge yourself to do it for more.
def system_of_linear_equations_solver(sub):
    #NOTE: tests may fail due to sets being randomly ordered, but the answers are correct
    r"""System of Linear Equations Checker/Solver.

    Checks whether a given string is a system of linear equations in two variables,
    and if so, returns an explanation of how to solve it.

    Parameters
    ----------

    sub : str
        The submitted expression, as a math string, to be passed to SymPy.

    Returns
    -------

    explanation:
        False if unable to parse as linear system,
        A worked thorugh $\LaTeX$ explanation otherwise.

    Examples
    --------

    >>> system_of_linear_equations_solver("")
    False

    >>> system_of_linear_equations_solver("something abstract")
    False

    >>> system_of_linear_equations_solver("x+1")
    False

    >>> print(system_of_linear_equations_solver("x=1"))
    False

    >>> print(system_of_linear_equations_solver("a=1,b=0"))
    False

    >>> print(system_of_linear_equations_solver("a=b+1,0=a-b"))
    False

    >>> print(system_of_linear_equations_solver("x+y=0,2x-y=9,2x+y=3"))
    False

    >>> system_of_linear_equations_solver("x**2+y=1,xy=1")
    False

    >>> print(system_of_linear_equations_solver("a+2b = 1,a-b=3"))
    Let's solve the system of equations:
    \[
        \begin{align*}
            a + 2 b&=1\\
            a - b&=3
        \end{align*}
    \]
    First we multiply each equation by the coefficient of $b$ in the other equations.
    This way they will all have the same coefficient for $b$.
    \begin{align*}
        -1\left(a + 2 b\right)&=-1\left(1\right)\\
        - a - 2 b&=-1
    \end{align*}
    \begin{align*}
        2\left(a - b\right)&=2\left(3\right)\\
        2 a - 2 b&=6
    \end{align*}
    If we subtract the second equation from the first, we get:
    \begin{align*}
        - 3 a&=-7
    \end{align*}
    Since this is now an equation in one variable, we can solve it like we would
    any other linear equation.
    \begin{align*}
    \end{align*}
    Let's solve the equation:
    \[
        - 3 a = -7
    \]
    We have just one term on the left:
    The variable $a$ with coefficient $-3$.
    Divide both sides by $-3$:
    \begin{align*}
        \frac{ - 3 a }{ -3 } &=
        \frac{ -7 }{ -3 } \\
        a &= \frac{7}{3}
    \end{align*}
    The equation is in the form $a = \frac{7}{3}$;
    That is, the value of $a$ is $\frac{7}{3}$.\begin{align*}
    \end{align*}
    Plugging in $\frac{7}{3}$ for $a$ in the first equation, we can now
    solve for $b$ like we would any other linear equation.
    \begin{align*}
    \end{align*}
    Let's solve the equation:
    \[
        2 b + \frac{7}{3} = 1
    \]
    First, we subtract 7/3 from both sides:
    \begin{align*}
        (2 b + \frac{7}{3})-(7/3) &= 1-(7/3) \\
        2 b &= - \frac{4}{3}
    \end{align*}
    We have just one term on the left:
    The variable $b$ with coefficient $2$.
    Divide both sides by $2$:
    \begin{align*}
        \frac{ 2 b }{ 2 } &=
        \frac{ - \frac{4}{3} }{ 2 } \\
        b &= - \frac{2}{3}
    \end{align*}
    The equation is in the form $b = - \frac{2}{3}$;
    That is, the value of $b$ is $- \frac{2}{3}$.\begin{align*}
    \end{align*}
    Thus we have found the pair of values which satisfy the two linear equations:
    $b=- \frac{2}{3}$ and $a=\frac{7}{3}$.
    <BLANKLINE>

    >>> print(system_of_linear_equations_solver("3x+2/3y=5/2,5x-y=2"))
    Let's solve the system of equations:
    \[
        \begin{align*}
            3 x + \frac{2 y}{3}&=\frac{5}{2}\\
            5 x - y&=2
        \end{align*}
    \]
    First we multiply each equation by the coefficient of $y$ in the other equations.
    This way they will all have the same coefficient for $y$.
    \begin{align*}
        -1\left(3 x + \frac{2 y}{3}\right)&=-1\left(\frac{5}{2}\right)\\
        - 3 x - \frac{2 y}{3}&=- \frac{5}{2}
    \end{align*}
    \begin{align*}
        \frac{2}{3}\left(5 x - y\right)&=\frac{2}{3}\left(2\right)\\
        \frac{10 x}{3} - \frac{2 y}{3}&=\frac{4}{3}
    \end{align*}
    If we subtract the second equation from the first, we get:
    \begin{align*}
        - \frac{19 x}{3}&=- \frac{23}{6}
    \end{align*}
    Since this is now an equation in one variable, we can solve it like we would
    any other linear equation.
    \begin{align*}
    \end{align*}
    Let's solve the equation:
    \[
        - \frac{19 x}{3} = - \frac{23}{6}
    \]
    We have just one term on the left:
    The variable $x$ with coefficient $- \frac{19}{3}$.
    Divide both sides by $- \frac{19}{3}$:
    \begin{align*}
        \frac{ - \frac{19 x}{3} }{ - \frac{19}{3} } &=
        \frac{ - \frac{23}{6} }{ - \frac{19}{3} } \\
        x &= \frac{23}{38}
    \end{align*}
    The equation is in the form $x = \frac{23}{38}$;
    That is, the value of $x$ is $\frac{23}{38}$.\begin{align*}
    \end{align*}
    Plugging in $\frac{23}{38}$ for $x$ in the first equation, we can now
    solve for $y$ like we would any other linear equation.
    \begin{align*}
    \end{align*}
    Let's solve the equation:
    \[
        \frac{2 y}{3} + \frac{69}{38} = \frac{5}{2}
    \]
    First, we subtract 69/38 from both sides:
    \begin{align*}
        (\frac{2 y}{3} + \frac{69}{38})-(69/38) &= \frac{5}{2}-(69/38) \\
        \frac{2 y}{3} &= \frac{13}{19}
    \end{align*}
    We have just one term on the left:
    The variable $y$ with coefficient $\frac{2}{3}$.
    Divide both sides by $\frac{2}{3}$:
    \begin{align*}
        \frac{ \frac{2 y}{3} }{ \frac{2}{3} } &=
        \frac{ \frac{13}{19} }{ \frac{2}{3} } \\
        y &= \frac{39}{38}
    \end{align*}
    The equation is in the form $y = \frac{39}{38}$;
    That is, the value of $y$ is $\frac{39}{38}$.\begin{align*}
    \end{align*}
    Thus we have found the pair of values which satisfy the two linear equations:
    $y=\frac{39}{38}$ and $x=\frac{23}{38}$.
    <BLANKLINE>

    >>> print(system_of_linear_equations_solver("3a+2b=5,a+2b=3"))
    Let's solve the system of equations:
    \[
        \begin{align*}
            3 a + 2 b&=5\\
            a + 2 b&=3
        \end{align*}
    \]
    If we subtract the second equation from the first, we get:
    \begin{align*}
        4 a&=4
    \end{align*}
    Since this is now an equation in one variable, we can solve it like we would
    any other linear equation.
    \begin{align*}
    \end{align*}
    Let's solve the equation:
    \[
        4 a = 4
    \]
    We have just one term on the left:
    The variable $a$ with coefficient $4$.
    Divide both sides by $4$:
    \begin{align*}
        \frac{ 4 a }{ 4 } &=
        \frac{ 4 }{ 4 } \\
        a &= 1
    \end{align*}
    The equation is in the form $a = 1$;
    That is, the value of $a$ is $1$.\begin{align*}
    \end{align*}
    Plugging in $1$ for $a$ in the first equation, we can now
    solve for $b$ like we would any other linear equation.
    \begin{align*}
    \end{align*}
    Let's solve the equation:
    \[
        2 b + 3 = 5
    \]
    First, we subtract 3 from both sides:
    \begin{align*}
        (2 b + 3)-(3) &= 5-(3) \\
        2 b &= 2
    \end{align*}
    We have just one term on the left:
    The variable $b$ with coefficient $2$.
    Divide both sides by $2$:
    \begin{align*}
        \frac{ 2 b }{ 2 } &=
        \frac{ 2 }{ 2 } \\
        b &= 1
    \end{align*}
    The equation is in the form $b = 1$;
    That is, the value of $b$ is $1$.\begin{align*}
    \end{align*}
    Thus we have found the pair of values which satisfy the two linear equations:
    $b=1$ and $a=1$.
    <BLANKLINE>

    >>> print(system_of_linear_equations_solver("x+y=5,x+y=3"))
    Let's solve the system of equations:
    \[
        \begin{align*}
            x + y&=5\\
            x + y&=3
        \end{align*}
    \]
    If we subtract the second equation from the first, we get:
    \begin{align*}
        0&=2
    \end{align*}
    But these values aren't equal, so there are no solutions to this system of equations.
    <BLANKLINE>

    >>> print(system_of_linear_equations_solver("x+y=5,2x+2y=10"))
    Let's solve the system of equations:
    \[
        \begin{align*}
            x + y&=5\\
            2 x + 2 y&=10
        \end{align*}
    \]
    First we multiply each equation by the coefficient of $y$ in the other equations.
    This way they will all have the same coefficient for $y$.
    \begin{align*}
        2\left(x + y\right)&=2\left(5\right)\\
        2 x + 2 y&=10
    \end{align*}
    If we subtract the second equation from the first, we get:
    \begin{align*}
        0&=0
    \end{align*}
    In this case, both variables ended up cancelling out since the two
    equations were scalar multiples of each other. Thus there are an
    infinite number of solutions to this system of equations.
    <BLANKLINE>
    """

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
