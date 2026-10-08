+++
id = "lemma-nagata-finite-type-ideal-compact"
kind = "lemma"
title = "A finite type ideal is compact in the lattice of quasi-coherent ideals"
order = 204
lean = ["AlgebraicGeometry.Scheme.IdealSheafData.exists_le_of_ofFiniteType_le_iSup", "AlgebraicGeometry.Scheme.IdealSheafData.exists_mem_le_of_ofFiniteType_le_sSup"]
+++
Let $X$ be quasi-compact, let $\mathcal A\subseteq\mathcal O_X$ be a finite
type quasi-coherent ideal, and let $(\mathcal B_\alpha)_\alpha$ be a nonempty
family of quasi-coherent ideals on $X$ which is directed under inclusion. If
$\mathcal A\subseteq\bigcup_\alpha\mathcal B_\alpha$, then
$\mathcal A\subseteq\mathcal B_{\alpha_0}$ for some single index $\alpha_0$.

## Proof

On an affine open $\operatorname{Spec}(R)$ the assertion is that a finitely
generated ideal of $R$ contained in the union of a directed family of ideals
is already contained in one member: each of the finitely many generators lies
in some member, and directedness produces a member above all of them. Since
$X$ is quasi-compact it is covered by finitely many affine opens, and
directedness once more produces a single index above the finitely many
indices obtained on the members of the cover. Containment of quasi-coherent
ideals may be checked on an affine cover, so that index works.
