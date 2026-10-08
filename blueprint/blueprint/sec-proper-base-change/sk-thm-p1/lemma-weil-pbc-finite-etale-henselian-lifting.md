+++
id = "lemma-weil-pbc-finite-etale-henselian-lifting"
kind = "lemma"
title = "Finite-etale lifting over a henselian pair"
order = 1124
uses = ["def-weil-pbc-strict-henselian-setup", "lemma-weil-pbc-finite-locally-constant-etale-equivalence"]
+++
If $(A,\mathfrak m)$ is henselian and $Y\to\operatorname{Spec}A$ is proper,
restriction from finite etale $Y$-schemes to finite etale $Y_0$-schemes is an
equivalence, including unique lifting of morphisms and group actions.

## Proof

We expand the equivalence used by Tag `0A5G`; its source locator is
Tag `0A48`. First suppose that $A$ is complete noetherian and put
$Y_r=Y\times_AA/\mathfrak m^{r+1}$. Formal etaleness and nilpotent
invariance of the etale site lift a finite etale $P_0\to Y_0$ uniquely to a
compatible system $P_r\to Y_r$. Finiteness can be checked modulo the
nilpotent ideal: on a finite affine cover
$Y_r=\bigcup_a\operatorname{Spec}R_{r,a}$, each lifted algebra is generated
by lifts of a finite set of generators of the $r=0$ algebra, and Nakayama
makes the resulting algebra finite. The transition isomorphisms on the
finitely many overlaps obey the cocycle equation because their restrictions
do and etale morphisms are formally unramified.

Grothendieck existence applied to the compatible finite algebras
$(p_r)_*\mathcal O_{P_r}$ algebraizes them to a coherent
$\mathcal O_Y$-algebra, hence to a finite morphism $P\to Y$ with special
fibre $P_0$. The etale locus of $P\to Y$ is open and contains $P_0$.
Every point of $P$ specializes to the closed fibre because $P$ is proper
over the local base; therefore the complementary closed non-etale locus is
empty. This proves essential surjectivity in the complete noetherian case.
For full faithfulness, a map $u_0:P_0\to Q_0$ has graph

$$
\Gamma_{u_0}:P_0\longrightarrow P_0\times_{Y_0}Q_0,
$$

which is an open-and-closed finite etale subscheme. Algebraize this graph to
$W\to P\times_YQ$. The projection $W\to P$ is finite etale and is an
isomorphism on the closed fibre; its isomorphism locus is open, and the
proper closed complement would meet the closed fibre if nonempty. Hence it
is empty, and $W\cong P$ gives the unique lift $u:P\to Q$.

Now suppose $A$ is a noetherian henselian local G-ring. Complete it to
$\widehat A$. The first step gives a finite etale cover over
$Y_{\widehat A}$. Choose a finite affine cover of $Y$, write the finitely
many cover algebras, overlap maps, and cocycle equations with finitely many
generators and relations, and descend all of them to a finite type
$A$-algebra
$A_i=A[x_1,\ldots,x_N]/(f_1,\ldots,f_M)$ inside $\widehat A$.
After increasing $i$, the descended map is finite etale. Approximation for
henselian G-rings gives a solution $(b_1,\ldots,b_N)\in A^N$ of all equations
with $b_j\equiv x_j\pmod{\mathfrak m}$. The induced retraction
$A_i\to A$ base-changes the descended cover to a finite etale cover of $Y$
with special fibre $P_0$. The graph argument proves full faithfulness.

For a general henselian local $A$, choose noetherian local G-rings $A_i$ from
finite-type $\mathbf Z$-models and write
$A=\varinjlim_iA_i^h$. Proper finite presentation gives an index $i_0$ and
a proper model $Y_{i_0}\to\operatorname{Spec}A_{i_0}^h$. A finite etale
cover, a morphism between two such covers, and an equality of two morphisms
are each finite presentation data; using a finite affine cover and the
finitely many overlap equations, they descend to one common $i\geq i_0$.
Thus

$$
\mathit{FEt}_Y=\varinjlim_i\mathit{FEt}_{Y_i},\qquad
\mathit{FEt}_{Y_0}=\varinjlim_i\mathit{FEt}_{(Y_i)_0},
$$

including the Hom sets. The equivalence at every henselian noetherian
G-ring stage gives the desired equivalence after the colimit. Finally an
action of a finite group consists of finitely many morphisms and finitely
many multiplication, unit, and inverse equations. Full faithfulness lifts
the morphisms and their equations uniquely, so group actions lift as well.
