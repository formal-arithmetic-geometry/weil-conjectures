## Worker report

The module Sheaf.RingTheory.NormalizedFiniteCoefficientTower states
NormalizedCoefficientTower.normalized_finite_coefficient_tower with a sorry proof.
The DAG statement is unchanged. Four auxiliary declarations are real constructions
belonging to this same notion: reducedTensor is Mathlib's TensorProduct quotiented
by Mathlib's nilradical, left and right compose the pure-tensor inclusions with the
quotient map, and leftAlgebra restricts the left map along the given ring algebra.
They introduce no new independent mathematical notion and no postponed proof.

Hypotheses, clause by clause:

- A and B have CommRing, IsDomain and IsDiscreteValuationRing instances. The map is
  algebraMap A B; hinj asserts injectivity and hlocal asserts pullback of maximal ideals.
- K and L are fields with IsFractionRing A K and IsFractionRing B L. The A/B/L and
  A/K/L scalar towers express that the inclusions are the given compatible ones.
- H and N are fields with Algebra K H, Algebra H N and the compatible K/N tower;
  FiniteDimensional K H and FiniteDimensional H N are exactly the two finiteness
  hypotheses. The A/H and A/N algebras and their scalar towers are the restrictions
  of these maps; they add no independent condition on the fields.
- E_H and E_N are reducedTensor K L H and reducedTensor K L N, explicitly quotient
  by all nilpotents, with no separability condition. R_H and R_N are integralClosure
  A H and integralClosure A N. C_H and C_N are integralClosure B of these reduced
  tensors with their given B-algebra structures.

Conclusions, clause by clause:

- e is the natural reduced coefficient transition, characterized on every pure
  tensor by e(l tensor h) = l tensor image(h). The first equation writes pure
  tensors as products of the canonical left and right images. c is its restriction
  to C_H and C_N, with the next equation fixing its value in E_N.
- The lower transition is Mathlib's (IsScalarTower.toAlgHom A H N).mapIntegralClosure.
  Its injectivity and RingHom.IsIntegral are stated explicitly, as are those of c.
- iH and iN are the lower-to-upper structural inclusions, characterized in the
  ambient reduced tensors by x mapping to 1 tensor x. The coefficient square is
  recorded by c(iH x) = iN(lowerTransition x).
- Every q in MaximalSpectrum C_H has Q in MaximalSpectrum C_N with comap c Q = q.
- n is q.asIdeal.comap iH, and its IsMaximal is an explicit conclusion.
- Aq and Bq are any realizations of localization at n and q, via maps a and b
  satisfying primeCompl.IsLocalizationMap. Their canonical quotient constructions
  Localization.AtPrime are included in this quantification. IsDomain witnesses
  and IsDiscreteValuationRing Aq/Bq assert both are DVRs. The chosen realization
  universes are the universes of the original rings, so the canonical constructions
  are always among the quantified rings.
- The map alpha into H extends R_H's inclusion and satisfies the fraction-field
  universal property (nonZeroDivisors Aq).IsLocalizationMap alpha. This asserts H
  is its fraction field. Lq is any field with beta : Bq -> Lq satisfying the same
  fraction-field universal property; the constructed H-algebra and map ab give
  the compatible lower-to-upper local inclusions and the canonical H-map into Lq.
- s extends C_H -> Bq -> Lq to the reduced tensor, and its value on the right H
  factor is the H-algebra map. j is the coefficient map E_N -> (Lq tensor_H N)_red,
  fixed on every pure tensor by s on L and the inclusion on N.
- Rloc is the localization of R_N at the image of R_H minus n under the lower
  transition; Cloc localizes C_N at c(C_H minus q). Both image submonoids are
  written explicitly, and arbitrary realizations r,d satisfying IsLocalizationMap
  include the actual Localization quotients specified by the node.
- rho and sigma are injective maps from these localized rings into N and the
  reduced branch tensor respectively. They extend the original inclusions and j.
  Their ranges are exactly the Subrings of elements integral over Aq and Bq,
  with the canonical structural ring maps alphaN and left.comp beta. An injective
  map with this range gives precisely the claimed canonical isomorphism onto the
  integral closure. On fractions these equations force x/s to map to x/s.
- delta connects these localizations and both the original numerator square and
  the ambient reduced-tensor square commute. This retains structural compatibility.
- For every maximal Q with contraction q, m = Q.comap iN is explicitly maximal.
  The extensions m.map r and Q.map d are asserted maximal in Rloc and Cloc.
  The direct localizations Localization.AtPrime m and Localization.AtPrime Q
  are domains and DVRs. a' and b' exhibit these actual direct rings as the
  localizations of the successive normalizations at those extended maximal ideals.
  Their numerator equations determine the canonical fraction identifications.
  ab' and its two equations give compatibility with the local lower-to-upper map.
- There are no completeness, separability, module-finiteness or residue-perfectness
  hypotheses. The six original object universes are independent and explicitly bound.

Using IsLocalizationMap avoids inserting local instances or hidden let/have
binders into the theorem statement. It is Mathlib's underlying universal-property
predicate used by IsLocalization and IsFractionRing, not a replacement definition.
Every existential ring homomorphism is pinned down on generating original ring
elements or pure tensors; localization and fraction-field uniqueness determine its
remaining values. No arbitrary map is supplied as an additional hypothesis.

Dependency declarations read and used:

- def-sc-discrete-valuation-ring: Mathlib.RingTheory.DiscreteValuationRing.Basic,
  IsDiscreteValuationRing, the nonfield local-PID class on domains.
- def-pc-field-extension: Mathlib.Algebra.Algebra.Defs, Algebra and algebraMap.
- def-weil-pbc-integral-closure:
  Mathlib.RingTheory.IntegralClosure.Algebra.Basic, integralClosure and IsIntegral;
  transition restriction uses AlgHom.mapIntegralClosure from
  Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic.
- def-weil-pbc-module-tensor-product: Mathlib.LinearAlgebra.TensorProduct.Defs,
  TensorProduct; Mathlib.RingTheory.TensorProduct.Basic and Maps supply its ring
  structure and canonical includeLeft/includeRight/productMap/ext interfaces.
- def-weil-pbc-localization-at-prime:
  Mathlib.RingTheory.Localization.AtPrime.Basic, Localization.AtPrime and primeCompl;
  Mathlib.GroupTheory.MonoidLocalization.Basic, Submonoid.IsLocalizationMap;
  Mathlib.RingTheory.Localization.FractionRing, IsFractionRing and nonZeroDivisors.
- Proof dependency modules imported non-publicly: Localization.Integral gives
  integralClosure.isFractionRing_of_finite_extension and IsLocalization.integralClosure;
  Flat.Basic gives Algebra.TensorProduct.includeLeft_injective; IsIntegralClosure.Basic
  gives isIntegral_trans; Spectrum.Prime.Topology gives RingHom.IsIntegral.comap_surjective;
  Ideal.GoingUp gives Ideal.isMaximal_of_isIntegral_of_isMaximal_comap'.
  Localization.AtPrime.Basic gives mapPiEvalRingHom_bijective. The tensor universal
  property is in the already publicly imported TensorProduct.Maps. No declared
  module exists for lem-sfb-dvr-algebraic-normalization-structure at reading time;
  it is only a proof dependency and is not required to form this statement.

Source checks: read Stacks more-algebra.tex remark-construction (09EM),
lemma-solutions-go-down and its proof (09ES), and algebra.tex
lemma-integral-closure-localize and proof (0307). The latest blueprint's
sk-thm-sf-ctf-stability-direct-images.proof.md has the direct-image argument, not
this historical auxiliary algebra assertion, as the node's accepted split reports.

Edge cases checked mathematically before writing: H=K, N=H and the whole identity
coefficient tower give identity comparisons. A split finite separable extension
can produce several E_H factors; localization chooses the q factor and kills the
others. A purely inseparable extension can give nonzero tensor nilpotents; the
nilradical quotient, and no unreduced tensor-is-field assertion, handles it.
Zero rings cannot occur as the initial fields or DVRs. Each displayed localization
has denominators disjoint from its prime; arbitrary maximal Q over q is retained.
Nothing assumes normalization finite as a module, or any residue field perfect.

Searches for an existing statement:

- msearch leanfinder: "Successive reduced field tensor products and local integral
  closures in finite coefficient towers have the same normalized DVR branches".
  Eight results, including TensorProduct.toIntegralClosure_bijective_of_tower,
  the localization variant, and Algebra.intNorm_eq_of_isLocalization. None states
  the reduced-tensor branch theorem: the first assumes other base-change
  comparisons, while the localization results supply only constituent steps.
- msearch loogle: "integralClosure, IsLocalization". Two hits:
  IsLocalization.integralClosure and
  TensorProduct.toIntegralClosure_bijective_of_isLocalization. Neither includes
  branch selection, field towers, DVRs or the simultaneous structural comparisons.
- msearch leansearch: "Integral closure localizations in successive finite field
  extensions and reduced tensor products". Eight hits: geometric reducedness
  results, isIntegral_localization, integralClosure localization and normality
  lemmas; no exact theorem.
- msearch grep: "def.*(map|lift)|theorem.*map" in RingTheory/IntegralClosure/Algebra.
  One hit, Algebra.IsIntegral.of_surjective. Direct rg then found and reused
  AlgHom.mapIntegralClosure in IsIntegralClosure/Basic rather than copying it.
- rg on Mathlib and project sources for reducedTensor/reduction definitions,
  integralClosure, normalized coefficient towers and normalization branches;
  grep of WeilConjectures for the blueprint id; and the upstream name index for
  NormalizedCoefficientTower/normalized_finite_coefficient_tower. No exact theorem
  or duplicate declaration name found. The reduced tensor abbreviation merely
  assembles the existing TensorProduct, quotient and nilradical constructions.

No statement correction, new DAG node, dependency module or disputed claim is needed.

## Second reading by Q65

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
