+++
id = "thm-weil-pbc-henselian-idempotent-lifting"
kind = "remark"
title = "Idempotent lifting for the structure sheaf over a henselian pair"
order = 1137
uses = ["def-weil-pbc-henselian-terminology", "def-weil-pbc-scheme-conventions", "thm-weil-pbc-stein-inputs"]
tags = ["latex:openproblem"]
+++
Let $(A,I)$ be a henselian pair and let $Z\to\operatorname{Spec}A$ be proper,
with closed fibre $Z_0=Z\times_AA/I$. Then every idempotent of
$H^0(Z_0,\mathcal O_{Z_0})$ lifts uniquely to an idempotent of $H^0(Z,\mathcal
O_Z)$; equivalently, restriction induces a bijection on idempotents, and the
open and closed subschemes of $Z_0$ are exactly the closed fibres of the open
and closed subschemes of $Z$. This statement is not proved in this blueprint;
it is the interface used by the finite-etale lifting theorem below.

(*The restriction map itself is **not** an isomorphism, and no such claim is
made:* for $A=k[[t]]$, $I=(t)$ and $Z=\mathbf P^1_A$ the map is $k[[t]]\to k$,
surjective but not injective. Only the idempotents are compared, and they
correspond to the open and closed subschemes of the two schemes. The statement
is the structure-sheaf counterpart of input (iii) of the Stein inputs: the
locally constant form of the Zariski restriction criterion does not apply to
the structure sheaf, which is not a torsion sheaf, so this idempotent
correspondence has to be supplied separately. Classically it is the
object-level half of the henselian-pair proper-base-change package, Stacks
Project, Etale Cohomology, Section 59.91, Tag
[0A0B](https://stacks.math.columbia.edu/tag/0A0B) (every connected component
of $Z$ meets $Z_0$, which gives the surjectivity on components, hence on
idempotents, while uniqueness follows because distinct clopens of $Z$ have
distinct traces on $Z_0$); the finite-etale forms are Tag
[0A0C](https://stacks.math.columbia.edu/tag/0A0C) and Tag
[0A3S](https://stacks.math.columbia.edu/tag/0A3S).)
