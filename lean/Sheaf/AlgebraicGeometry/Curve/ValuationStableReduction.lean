/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q08
-/
module

public import Sheaf.AlgebraicGeometry.MultipointedCurveModification
public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.RingTheory.Valuation.ValuationSubring

import Sheaf.AlgebraicGeometry.ValuationSemistableStableContraction
import Mathlib.AlgebraicGeometry.Gluing
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Sheaf.AlgebraicGeometry.BirationalQuasiModificationCommonCover
import Sheaf.AlgebraicGeometry.Curve.StableModificationUniquenessNormal
import Sheaf.TraceFormula.ValuationHorizontalCurveModels
import Sheaf.TraceFormula.ValuationMarkingSemistableSeparation
import Sheaf.TraceFormula.ValuationStrictSemistableCofinality
import Sheaf.TraceFormula.ValuationStrictSemistableLocalUniformization

/-! # Stable reduction over a finite-height separably closed valuation field

Source: Temkin, Stable modification of relative curves, Proposition 4.5.1, p. 33,
smooth-generic-fibre case (blueprint: lem-trf-valuation-stable-reduction).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.MultipointedCurve

/-- Stable reduction over the valuation ring itself, without a base extension.
The finite prime spectrum expresses finite height, since the primes of a valuation
ring are linearly ordered. The valuation subring has fraction field `K`.
Source: Temkin, Proposition 4.5.1, p. 33, smooth-generic-fibre case.
(blueprint: lem-trf-valuation-stable-reduction)

Proof:
1. Apply [lem-trf-valuation-horizontal-curve-models] to $(X,D)$. In particular $X$ is reduced with
finitely many components, and any reduced modification of $X$ is again a finitely presented flat
$T$-curve, with the marking extended by schematic closure. It is legitimate to work with the
centred valuations of each generic component separately; no assertion that connectedness of $X$
forces connectedness of $X_\eta$ is needed. The empty curve case has the identity stable
modification, so assume $X$ nonempty. Apply
[lem-trf-valuation-strict-semistable-local-uniformization] to get finitely many integral strictly
semistable quasi-modifications $Y_i\to X$ on which all these valuations have centres. All generic
opens of $Y_i$ are smooth.

2. Use [lem-trf-birational-quasi-modification-common-cover] on this finite valuation cover. It
gives a reduced proper modification $X_1\to X$ and an open cover $X_1=\bigcup W_i$, with
modifications $W_i\to Y_i$ over $X$. Here $X$ is quasi-compact and quasi-separated because it is
finitely presented over the affine base. By [lem-trf-valuation-horizontal-curve-models],
$(X_1,D_1)$, with $D_1$ the closure of $D_\eta$, is a multipointed $T$-curve and an
$\eta$-modification of $(X,D)$. Its restriction $(W_i,E_i)$ is the horizontal marked model on
$W_i$. The generic fibre of $W_i\to Y_i$ is an isomorphism, since it is a modification of a smooth
curve, as included in the same horizontal-model node applied to $Y_i$ with empty marking.

3. Fix $i$. Apply [lem-trf-valuation-strict-semistable-cofinality] to the modification $W_i\to
Y_i$ of the strictly semistable $T$-curve $Y_i$. Obtain a strictly semistable $Z_i$ with an
$\eta$-modification $Z_i\to W_i$. Since $Z_i$ is a $T$-curve with smooth generic fibre
$Z_{i,\eta}\cong W_{i,\eta}$, the reducedness clause of
[lem-trf-valuation-horizontal-curve-models] applied to $(Z_i,\emptyset)$ shows that $Z_i$ is
reduced, so $Z_i\to W_i$ is a reduced modification. Give $Z_i$ the schematic closure $F_i$ of the
generic marking of $W_i$. By [lem-trf-valuation-horizontal-curve-models], this is a multipointed
curve and $(Z_i,F_i)\to(W_i,E_i)$ is an $\eta$-modification of pairs; importantly, one does not
take the full inverse image of the marking. The generic marking is etale and the generic curve is
smooth. Thus [lem-trf-valuation-marking-semistable-separation] gives a semistable
$\eta$-modification $(\widetilde Z_i,\widetilde F_i)\to(Z_i,F_i)$. Composing the two proper maps,
on both curves and markings, gives a semistable $\eta$-modification of $(W_i,E_i)$ by
[lem-weil-pbc-proper-fp-permanence](a). For schematic density of the composite, intersect the two
dense isomorphism opens where the composition is defined by isomorphisms. This intersection is
dense on every component of the smooth generic fibre. On each flat affine chart its ring injects
into its generic localization, a reduced ring, and then into sections on this generic dense open.
Thus the intersection is schematically dense on source and target.

4. Apply [lem-trf-valuation-semistable-stable-contraction] to each semistable modification from
Step 3, obtaining a stable $\eta$-modification $f_i:(S_i,H_i)\to(W_i,E_i)$. These are stable
relative to $W_i$, not yet relative to $X$. Restrict to $W_{ij}=W_i\cap W_j$. The restrictions are
still multipointed curves and proper $\eta$-modifications, using
[lem-trf-valuation-horizontal-curve-models] for closures and generic identifications and
[lem-weil-pbc-proper-fp-permanence](b) for properness. They are semistable because this is a
condition on the local rings and the marking. Stability is preserved under this target
restriction: a contracted component over a point of $W_{ij}$ is entirely contained in its inverse
image, and its marking and singular intersection points are the same as before restriction. Thus
an exceptional projective line here would already be exceptional for $f_i$.

5. The base $T$ is normal: if $z\in K\setminus V$ were integral over $V$, then $z^{-1}$ would be a
nonunit of $V$; multiplying a monic integral equation for $z$ by $z^{-n}$ would give
$1\in(z^{-1})$, a contradiction. Localizations of $V$ are valuation rings by the same divisibility
test and are integrally closed by the same argument. The affine integral scheme $T$ is also
quasi-compact and quasi-separated. Consequently [lem-trf-stable-modification-uniqueness-normal]
applies to the two restricted stable modifications of $(W_{ij},D_1|_{W_{ij}})$: their generic
curve is smooth, their generic marking is etale, and their generic identifications agree. It
yields a unique isomorphism $\alpha_{ij}$ over this pair. Empty intersections use the unique empty
isomorphism. On a triple overlap both $\alpha_{jk}\alpha_{ij}$ and $\alpha_{ik}$ are isomorphisms
over the same target pair; uniqueness makes them equal. This supplies the cocycle, rather than
assuming that chosen local models agree.

6. Apply [lem-weil-pbc-glue-schemes] separately to the $S_i$ and to the $H_i$, with the inverse
images of $W_{ij}$ as overlap opens and the cocycle of Step 5. This produces $(S,H)$ over
$(X_1,D_1)$. Maps to the target and the marking immersions glue: their continuous maps and sheaf
homomorphisms agree on intersections, and the marking ideals agree there. The result is a closed
marking. Flatness, finite presentation and the pure fibre dimensions hold on these finite open
covers; for finite presentation, quasi-compactness and quasi-separatedness follow by gluing over
the finite cover $W_i$ of the finitely presented $X_1$. Semistability is checked in the same local
rings as before. Properness of both pair maps is local on the target: finite type and the closed
diagonal are local there, and closed images after any base change are checked on the corresponding
open cover. Hence the glued pair map is proper. Its generic fibre is the identity by the chosen
identifications, and its local dense isomorphism opens give schematic density as in Step 3.
Finally, every contracted projective-line component is contained in the inverse image of some
$W_i$, so the same argument as Step 4 proves stability relative to $(X_1,D_1)$. We have
constructed a semistable (indeed stable) $\eta$-modification of $(X_1,D_1)$.

7. Compose $(S,H)\to(X_1,D_1)\to(X,D)$. Both maps on the curve and marking are proper, so their
composites are proper by [lem-weil-pbc-proper-fp-permanence](a). They are generic-fibre
isomorphisms; intersect their dense isomorphism opens as in Step 3. The intersection is dense on
each component of the generic curve (and is the whole generic marking); injection of flat affine
rings into generic localizations and then into sections on these dense opens proves schematic
density. Thus the composite is a semistable $\eta$-modification of $(X,D)$. It need not be stable
relative to $X$, since the intermediate map may contract more components. Apply
[lem-trf-valuation-semistable-stable-contraction] once more, now relative to $(X,D)$, to obtain
the required stable $\eta$-modification over $T$ itself. No extension of the valuation field or
alteration of $T$ was introduced. -/
theorem exists_stableEtaModification_of_isSepClosed
    (K : Type u) [Field K] [IsSepClosed K] (V : ValuationSubring K)
    [Finite (PrimeSpectrum V)] (C : MultipointedCurve (Spec (.of V)))
    (hsmooth : Smooth (pullback.snd C.x (Spec.map (CommRingCat.ofHom V.subtype))))
    (hmarking : Etale (pullback.snd C.d
      (Spec.map (CommRingCat.ofHom V.subtype)))) :
    ∃ C' : MultipointedCurve (Spec (.of V)), ∃ f : Hom C' C,
      f.IsStable (Spec.map (CommRingCat.ofHom V.subtype)) := by
  sorry

end AlgebraicGeometry.MultipointedCurve
