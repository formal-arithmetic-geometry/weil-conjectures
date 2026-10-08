+++
id = "def-nagata-admissible-blowup"
kind = "definition"
title = "$U$-admissible blow-up, [stacks-project]"
order = 60
lean = ["AlgebraicGeometry.IsAdmissible"]
uses = ["def-nagata-global-blowup"]
+++
Let $U\hookrightarrow X$ be a quasi-compact open immersion. A
*$U$-admissible blow-up datum* consists of a finite type
quasi-coherent ideal $\mathcal I\subseteq\mathcal O_X$ with
$\mathcal I|_U=\mathcal O_U$, a morphism
$\pi\colon X'\to X$, and a specified isomorphism
$X'\cong\operatorname{Bl}_{\mathcal I}(X)$ over $X$. A morphism equipped
with such data is called a $U$-admissible blow-up. The definition records
the ideal and the identification with its blow-up; the equivalent
finite-presentation closed-center formulation is stated separately once
the required ideal/closed-immersion comparison is available.
