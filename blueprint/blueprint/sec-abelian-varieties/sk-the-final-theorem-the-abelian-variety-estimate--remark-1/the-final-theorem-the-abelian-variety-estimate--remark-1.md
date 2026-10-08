+++
id = "the-final-theorem-the-abelian-variety-estimate--remark-1"
kind = "remark"
order = 595
+++
*Where this feeds in.*

- **Smooth base change** ([sec-smooth-base-change],
the bad-prime computation of the eight curve assertions): clauses (a)
and (b) supply that the $p$-torsion group scheme of the Jacobian is
finite flat of order $p^{2g_{C_0}}$ (blueprint
lem:sc-isogeny-facts(b) with lem:sc-mult-n-finite-flat), so
that the Artin–Schreier kernel is finite; [lem-sc-lang-steinberg]
supplies the surjectivity of the Artin–Schreier map $\wp$ on
$H^1(C_0,\cO)$ (blueprint lem:sc-lang-steinberg), and
[lem-sc-fixed-points-finite], [lem-sc-frobenius-fixed-invariance] supply the
$p$-linear fixed-point comparison in characteristic $p$.
- **Monodromy and the curve argument**
([sec-purity-real-sheaves], the Jacobian torsion data of
[def-sc-jacobian]): clause (c) gives
$A[\ell^n](k)\cong(\Z/\ell^n\Z)^{2g}$ and its base-change invariance
(blueprint lem:sc-ntorsion-etale); clause (d) gives the
divisibility used to see that the transition maps are surjective
(lem:sc-isogeny-surjective) and $T_\ell J\cong\Z_\ell^{2g}$.
The Kummer identification
$H^1(C,A_n(1))\cong J[\ell^n](\overline{k}_0)$ and the dual form
$\varprojlim H^1(C,A_n)\cong\Hom_{\Z_\ell}(T_\ell J,\Z_\ell)$ that the
whole real-purity argument runs on are not part of this section; they
belong to the real-purity section, built on [def-sc-jacobian] (blueprint
lem:wf-curve-kummer-jacobian-tate-module,
lem:wf-curve-h1-dual-tate-module), with the semilinear Galois
action coming from the functoriality of the Jacobian.
- **Jacobian**: the Jacobian itself is constructed later, in
[thm-sc-jacobian-representability] of [sec-picard-framework], resting on
[thm-pc-picard-representable], and over an arbitrary field in
[thm-pd-jacobian-general-field]. In the detailed blueprint these are
thm:sc-jacobian-representability (with thm:sc-theorem-of-the-base,
lem:sc-pic-tangent-space, def:sc-jacobian,
lem:sc-jacobian-unique) and thm:pd-jacobian-general-field.

*Every node is a separate statement*, per the
separation-of-conclusions rule. The external inputs are listed in the
last column of the table below; the largest are the theorem of the
cube ([thm-sc-theorem-of-cube]), projectivity ([lem-sc-abelian-variety-projective]),
the rigidity lemma ([lem-sc-rigidity]), the quoted isogeny facts
([lem-sc-mult-n-finite-flat]), the $p$-power order of connected finite group
schemes ([lem-sc-connected-finite-order]), Cartier's theorem
([lem-sc-fg-order-prime-etale]). Corresponding detailed blueprint source:
06e\_abelian\_varieties.tex (chapter chap:abelian-varieties),
with 06d\_group\_schemes.tex, 06f\_divisors\_picard\_riemann\_roch.tex,
50\_picard\_scheme\_of\_a\_curve\_new.tex, 06b\_jacobian.tex and
51\_general\_field\_picard.tex.

**Node-to-blueprint map.**

| node | detailed blueprint label | quoted external input |
| --- | --- | --- |
| [lem-sc-abelian-variety-characterization] | lem:sc-abelian-variety-characterization | `03RO`, `0H2U`, `0B7Q`, `0BFC` |
| [lem-sc-abelian-variety-projective] | lem:sc-abelian-variety-projective | `0BF7`, `0B45` |
| [lem-sc-ample-tensor] | lem:sc-ample-tensor | `0890` |
| [thm-sc-theorem-of-cube] | thm:sc-theorem-of-cube | `0BFE`, `0BF4` |
| [lem-sc-mult-n-pullback] | lem:sc-mult-n-pullback | `0BFF` |
| [lem-sc-deg-pullback-finite] | lem:sc-deg-pullback-finite | `0BEX` |
| [lem-sc-constant-locus-closed], [lem-sc-finite-image-locus-open] | lem:sc-constant-locus-closed, lem:sc-finite-image-locus-open | `01UA`, `0AH8` |
| [lem-sc-rigidity] | lem:sc-rigidity | `0BUG` (Step 4); cf. Milne I, Mumford II.6 |
| [lem-sc-av-commutative] | lem:sc-av-commutative | `0BFD` (alternative) |
| [lem-sc-mult-n-homomorphism] | lem:sc-mult-n-homomorphism (`06d`) | — |
| [cor-pqf-proper-quasifinite-finite] | thm:pqf-finite-iff-proper-finite-fibres | `02OG` |
| [lem-sc-ample-positive-degree] | lem:sc-ample-positive-degree | `0B5X` |
| [lem-sc-mult-n-finite-kernel], [lem-sc-mult-n-isogeny] | lem:sc-mult-n-isogeny | `03RP`, `0BFG` |
| [lem-sc-isogeny-degree] | lem:sc-isogeny-degree | — |
| [lem-sc-mult-n-finite-flat] | lem:sc-isogeny-facts, lem:sc-mult-n-finite-flat | `0BFG`, `03RP`, `0BFH`, `0BEV` |
| [lem-sc-connected-finite-order] | lem:sc-connected-finite-order | Milnor–Moore, Waterhouse Ch. 11 |
| [lem-sc-fg-order-prime-etale] | lem:sc-fg-order-prime-etale | `047N` (Cartier) |
| [lem-sc-finite-etale-points] | lem:sc-finite-etale-points | — |
| [lem-sc-ntorsion-etale] | lem:sc-ntorsion-etale | — |
| [lem-sc-isogeny-surjective] | lem:sc-isogeny-surjective | `03RP` |
| [lem-sc-divisible-group-structure] | lem:sc-divisible-group-structure | `03RP` (proof of (7)) |
| [prop-av-tate-rank] | def:wf-abelian-tate-module (`52`) with lem:sc-ntorsion-etale | — |
| [lem-sc-fixed-points-finite], [lem-sc-lang-steinberg], [lem-sc-frobenius-fixed-invariance] | lem:sc-fixed-points-finite, lem:sc-lang-steinberg, lem:sc-frobenius-fixed-invariance | `0ASV` |