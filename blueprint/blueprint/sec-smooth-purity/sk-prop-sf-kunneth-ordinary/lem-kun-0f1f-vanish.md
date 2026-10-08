+++
id = "lem-kun-0f1f-vanish"
kind = "lemma"
title = "Vanishing for sheaves supported on closed points"
order = 1766
uses = ["def-kun-separably-closed", "def-kun-support", "lem-kun-03qu-sep-closed", "lem-kun-04ca", "lem-kun-closed-point-field", "lem-kun-cp-approximation", "lem-kun-leray-bdd", "lem-kun-leray-finite", "lemma-weil-pbc-finite-direct-image-exact", "sbc-lem-higher-direct-image-limit"]
+++
Let $K$ be a separably closed
field and $X$ a scheme of finite type over $K$. Let $F$ be an
abelian sheaf on $X_{\Et}$ whose support
is contained in the set of
closed points of $X$. Then
$H^q(X_{\Et},F)=0$ for $q>0$. (*Source:* Stacks Project,
Tag [0F1F](https://stacks.math.columbia.edu/tag/0F1F), first
assertion.)

## Proof

The scheme $X$ is Noetherian because it is of finite type over a
field. The set of closed points is closed under specialization, and
the support of $F$ is contained in it, so the approximation
[lem-kun-cp-approximation] writes $F=\varinjlim_iF_i$ as a
filtered colimit of finitely generated subsheaves $F_i$, the support
of each $F_i$ being a finite set $Z_i$ of closed points of $X$.
Give $Z_i$ its reduced
closed subscheme structure and write $i:Z_i\to X$ for the closed
immersion. By [lem-kun-04ca] the sheaf $F_i$ is of the form
$i_*\mathcal G_i$ for a sheaf $\mathcal G_i$ on
$(Z_i)_{\Et}$, and by [lem-kun-closed-point-field] every
closed point of $X$ has a residue field which is a finite, purely
inseparable, hence separably closed extension of $K$; so $Z_i$ is
a finite disjoint union of spectra of separably closed fields.
By [lem-kun-03qu-sep-closed] (on each component, with
$H^q$ of a disjoint union being the direct sum of the $H^q$ of the
components) we get $H^q((Z_i)_{\Et},\mathcal G_i)=0$ for $q>0$.
Since $i$ is finite,
[lemma-weil-pbc-finite-direct-image-exact] and
[lem-kun-leray-bdd] (or [lem-kun-leray-finite]) give
$H^q(X_{\Et},F_i)=H^q((Z_i)_{\Et},\mathcal G_i)=0$ for $q>0$.
Finally, the higher-direct-image limit formula
[sbc-lem-higher-direct-image-limit] of the smooth-base-change chapter, applied to the
constant inverse system $X_i=X$ with the compatible system of sheaves
$F_i$, shows that cohomology commutes with the filtered colimit:
$H^q(X_{\Et},F)=\varinjlim_iH^q(X_{\Et},F_i)=0$ for $q>0$.
