#!/usr/bin/env python3
from flask import Flask, request, render_template
from equationsolvers import equation_solvers as solvers

app = Flask("Solver Website")

@app.route('/')
def solve():
    sub = request.args.get('sub', default='')

    if sub != '':
        for solver in solvers:
            workthrough = solver(sub)
            if workthrough != False:
                break
        else:
            workthrough = "Unable to understand expression '{}'".format(sub)
        return render_template('index.html',workthrough = workthrough)
    return render_template('index.html')

if __name__ == "__main__":
    app.run(debug=True)
