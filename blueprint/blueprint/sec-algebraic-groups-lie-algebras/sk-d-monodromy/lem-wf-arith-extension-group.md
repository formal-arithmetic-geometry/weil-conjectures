+++
id = "lem-wf-arith-extension-group"
kind = "lemma"
title = "The arithmetic monodromy extension is a group"
order = 2507
uses = ["def-wf-arithmetic-monodromy-extension", "def-wf-geometric-monodromy-group", "lem-wf-conjugation-geometric-monodromy"]
+++
In the situation of [def-wf-arithmetic-monodromy-extension], the
multiplication $(h,m)(h',n)=(h\alpha^m(h'),m+n)$ makes
$G_{\mathrm{arith}}(\rho)$ a group with identity $(1,0)$ and inverses
$(h,m)^{-1}=(\alpha^{-m}(h^{-1}),-m)$, and the degree map $\deg_G$
of [def-wf-arithmetic-monodromy-extension] is a surjective group
homomorphism with kernel $H_{\mathrm{geom}}\times\{0\}$, where
$H_{\mathrm{geom}}$ is the geometric monodromy group of
[def-wf-geometric-monodromy-group].

## Proof

By [lem-wf-conjugation-geometric-monodromy], $\alpha$ is an
automorphism of the group $H_{\mathrm{geom}}$ of
[def-wf-geometric-monodromy-group], so each power $\alpha^m$ is a
group automorphism and $\alpha^{m+n}=\alpha^m\circ\alpha^n$. The
displayed product is therefore associative:

$$
(h,m)\bigl((h',n)(h'',p)\bigr)
=(h\alpha^m(h')\alpha^{m+n}(h''),m+n+p)
=\bigl((h,m)(h',n)\bigr)(h'',p).
$$

The element $(1,0)$ is a two-sided identity because
$\alpha^m(1)=1$, and the displayed formula for $(h,m)^{-1}$ is a
two-sided inverse because $\alpha^{-m}(\alpha^m(h'))=h'$. Finally
$\deg_G\bigl((h,m)(h',n)\bigr)=m+n =\deg_G(h,m)+\deg_G(h',n)$, so $\deg_G$ is a homomorphism; it is
surjective since $\deg_G(1,m)=m$, and its kernel is the set of pairs
$(h,0)$, namely $H_{\mathrm{geom}}\times\{0\}$, as in
[def-wf-arithmetic-monodromy-extension].
