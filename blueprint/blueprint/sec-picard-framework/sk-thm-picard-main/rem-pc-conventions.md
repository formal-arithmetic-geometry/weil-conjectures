+++
id = "rem-pc-conventions"
kind = "remark"
title = "The meaning of ``curve'' and the role of separably closedness"
order = 838
+++
In Stacks Project, Chapter 44, a *smooth projective curve over $k$*
is a variety (integral, separated, finite type, dimension $1$) which is
smooth and projective over $k$
([def-pc-smooth-projective-curve]); the proof of Proposition
44.6.6 only uses this in combination with the fact that, for $k$
separably closed, all base changes $X_K$ are again smooth projective
curves ([prop-pc-xk-integral]), which is what the geometric
arguments (the Cartier criterion, the density of rational points, the
DVR computations) need. This is the reason why the individual lemmas
of the chain are stated for separably closed $k$ —Stacks states
44.6.2–44.6.4 for arbitrary fields, but in the proof of 44.6.6 they
are only used in the separably closed case (the deeper geometric
irreducibility of $X$ is automatic then; cf. [prop-pc-xk-integral]
and the discussion in [thm-pc-picard-representable]). The proof of
[prop-pc-xk-integral] uses the ``smoothness'' route
(smooth $\Rightarrow$ regular $\Rightarrow$ normal $\Rightarrow$
decomposition into integral components, with connectedness); the
classical alternative route goes through the fact that $\bar k/k$ is
purely inseparable ([lem-pc-kbar-pure-insep]), the homeomorphism
statement [lem-pc-homeo-pure-insep], and the equivalence
$H^0=k\Leftrightarrow$ geometrically connected
([lem-pc-h0-geom-connected]) —all of which are recorded above,
even though the smoothness route is the one used in the proof.
