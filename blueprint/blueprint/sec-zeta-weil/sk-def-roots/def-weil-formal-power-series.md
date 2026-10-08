+++
id = "def-weil-formal-power-series"
kind = "definition"
title = "Formal power series"
order = 2861
+++
For a commutative ring $R$, an element of $R[[T]]$ is a sequence
$(c_n)_{n\geq0}$ in $R$, written $\sum_{n\geq0}c_nT^n$.
Addition is coefficientwise, and the coefficient of $T^n$ in a
product is $\sum_{i=0}^n c_i d_{n-i}$.

*Mathlib:* `PowerSeries`. A basic Mathlib notion, used throughout, so it is not mapped as the Lean declaration of this object.
