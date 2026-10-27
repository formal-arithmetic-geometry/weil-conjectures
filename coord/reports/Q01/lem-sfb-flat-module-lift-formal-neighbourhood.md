## Worker report

The module Sheaf.RingTheory.FlatModuleLiftFormalNeighbourhood states
`Algebra.flatModuleLift_formalNeighbourhood_iff`. Its only theorem proof is `sorry`.
There are two real helper definitions belonging to this statement:
`Algebra.HasCoefficientFlatModuleLift` expands the existential flat module together
with its reduction isomorphism, and `Algebra.formalNeighbourhoodSpecialFibreMap`
is the tensor product of the identity on A and the supplied map S' → T'.
No new mathematical notion or independent DAG node is needed.

The preserved earlier worker ending concerns stage 1. The current node is split,
reviewed PASS, has no Lean record, and is listed in coord/queue.tsv for stage 2.
The stage-handoff paragraph of coord/brief-stage2.md expressly authorizes this work.
The accepted statement and split are unchanged.

Hypotheses and clauses, read against the node:

- A', A, S', T' are commutative rings: four Type u binders and CommRing instances.
  All four are Noetherian by their IsNoetherianRing instances.
- A' → A is the supplied algebraMap, surjective by hsurj, with square-zero kernel
  by hsquare: RingHom.ker (algebraMap A' A) ^ 2 = ⊥.
- The specified maps A' → S' → T' are algebraMaps; IsScalarTower A' S' T'
  fixes their composite, rather than assuming another unrelated coefficient map.
  Their flatness is precisely hflatS and hflatT, using RingHom.Flat.
- S and T are A ⊗[A'] S' and A ⊗[A'] T'. This merely switches the order of the
  factors in the node using tensor commutativity. These are the literal scalar
  extensions, not arbitrary algebras with assumed comparisons. Surjectivity of
  A' → A canonically identifies them with S'/IS' and T'/IT'.
- The induced S → T is formalNeighbourhoodSpecialFibreMap. It is constructed by
  Algebra.TensorProduct.map (AlgHom.id A' A) (IsScalarTower.toAlgHom A' S' T'),
  hence sends a ⊗ s to a ⊗ image(s).
- K' is an Ideal S'. hquot is Function.Bijective of Ideal.quotientMap along
  algebraMap S' T', with target ideal K'.map (algebraMap S' T'). Bijectivity of
  this canonical ring map is exactly its being an isomorphism.
- M is a ModuleCat over S. Module.Finite S M says finitely generated, and hflatM
  says Module.Flat A after restricting along the canonical A → S.
- hlocal ranges over every g : S' satisfying g ∈ K'. Its source is
  Localization.Away g. Its reduction map is Localization.awayMap of the
  canonical S' → S, with target Localization.Away (image(g)). Its module is
  ModuleCat.extendScalars (algebraMap S (Localization.Away (image(g)))) applied
  to M. This is S_g ⊗[S] M, canonically M ⊗[S] S_g.
- HasCoefficientFlatModuleLift requires an existential module L_g flat over A'
  via A' → S' → S'_g, together with Nonempty of the S_g-module isomorphism
  S_g ⊗[S'_g] L_g ≅ M_g. Since S_g = S'_g ⊗[A'] A, this is exactly
  L_g ⊗[A'] A with its specified induced S_g action. Nonempty records existence
  of the specified isomorphism as part of the existential assertion.
- The left side of the conclusion uses the canonical S' → S and coefficient
  map A' → S', so gives precisely the S'-module L, A'-flatness, and S-linear
  reduction isomorphism. The right side uses T' → T and A' → T', with target
  extendScalars of the canonical S → T applied to M, hence M ⊗[S] T.
  The connective is iff and the witnesses on its two sides are independent.

The helper uses ModuleCat.extendScalars, whose object is the actual ordinary
TensorProduct (ChangeOfRings.lean:376–403), and ModuleCat.restrictScalars, whose
object uses Module.compHom (same file:65–88). No hollow definition, arbitrary
comparison, derived replacement, extra flatness, or finite-generation requirement
on the lift has been introduced. The module universe is max u v throughout.
All rings can be raised to a common u; v permits modules larger than the rings.
For finite M over a nilpotent coefficient quotient any existing lift is finite
(by lifting generators and nilpotent Nakayama), hence has a representative in
this module universe; the existential universe does not restrict liftability.
All universes and variables are explicitly bound and autoImplicit is false.

Dependency declarations used:

- def-weil-pbc-noetherian-ring: Mathlib.RingTheory.Noetherian.Defs,
  IsNoetherianRing (every ideal finitely generated).
- def-weil-pbc-flat-ring-map: Mathlib.RingTheory.RingHom.Flat, RingHom.Flat,
  and Mathlib.RingTheory.Flat.Basic, Module.Flat. Read the defining class and
  the equivalence with preservation of injective tensor maps.
- def-weil-pbc-module-tensor-product: Mathlib.LinearAlgebra.TensorProduct.Defs,
  TensorProduct, and its genuine functorial interface ModuleCat.extendScalars.
  Its mathlib_match suffices although the node has no lean field.
- def-weil-ring-localization-away: Mathlib.GroupTheory.MonoidLocalization.Away,
  Localization.Away, with the ring structure and canonical awayMap imported
  from Mathlib.RingTheory.Localization.Away.Basic.

Proof imports include every recorded proof module: the localization-flat
Mathlib module, NoetherianPseudoCoherentCohomologyCriterion,
PseudoCoherentRHomFlatBaseChange, and the upstream
TorsionSubmoduleFlatBaseChangeIso module. The two freshly split module-obstruction
nodes and lem-trf-flat-projective-hom-models have no usable lean or mathlib_match
record, so there is no module to import for them yet. They are proof-only inputs,
not prerequisites for typing the statement. Their names and full argument remain
in the theorem docstring, following the accepted five-step DAG proof.

Edge cases checked before writing:

- K' = 0: its only localization condition is at g = 0; the local ring and
  localized module are zero. The assumed quotient comparison then is S' ≅ T',
  giving precisely the expected equivalence. No Nontrivial assumption excludes it.
- K' = ⊤: g = 1 is among the local hypotheses, already supplying the global
  lift. The forward implication is the flat scalar-extension construction.
- M = 0: zero lifts exist on both sides, and Module.Finite and Module.Flat hold.
- I = 0: the reduction A' → A is an isomorphism, and M itself supplies a lift.
- Zero rings and nilpotent localization elements are admitted, including g = 0.
- The two module isomorphisms are linear over S and T respectively, not merely
  A-linear. No restriction on characteristic or on the size of a generating set.

Source read: literature/stacks-project/examples-defos.tex:1940–2075, Tags 0DZ1
and 0DZ2, including the finite-M use in the RHom base-change line and its
free-resolution footnote. The accepted node already restricts the displayed
nilpotent assertion to the square-zero argument and makes finiteness explicit.
No additional source error or statement correction is being introduced here.

Searches (2026-10-23):

- msearch.py leanfinder: "A finite module flat over a square zero quotient admits
  a flat lift if and only if its flat formal neighbourhood base change does,
  given local lifts off an ideal". Eight hits, headed by
  Algebra.FormallyUnramified.flat_of_restrictScalars, Module.flat_of_isLocalized_span,
  Algebra.FormallySmooth.flat_of_algHom_of_isNoetherianRing, and
  Algebra.FormallySmooth.iff_injective_cotangentComplexBaseChange. These concern
  flatness of given modules or formal smoothness, not existence of module lifts.
- msearch.py loogle: "Flat", "lift". Eleven hits, including Module.Flat.of_ulift,
  Module.Flat.ulift, the ulift_iff lemmas, and cotangent exactness. None is the
  claimed deformation comparison.
- msearch.py grep: lift.*flat|flat.*lift|liftability in RingTheory. Eighteen hits
  concerning ulift, flat base change of cotangent modules, and faithful flatness;
  no matching statement.
- rg on lean/WeilConjectures and lean/Sheaf with
  lift.*flat|flat.*lift|FlatModuleLift|flatModuleLift and the node id found
  CompletionReflectsFlatLiftability (a consumer), local projectivity criteria,
  flat algebra lift statements, and other unrelated lifts. No matching theorem
  or existing flat-module-lift predicate.
- rg of the three newly introduced declaration names in Mathlib, WeilConjectures,
  Sheaf, and dag/lean_names_upstream.json found no collision.

No STATEMENT-DISPUTED issue remains.

## Second reading by Q01

A separate final reading in this worker (the dispatcher explicitly prohibits
starting another agent) compared the node and the source signature clause by
clause. In particular: four Noetherian rings, the surjection and square-zero
kernel, both flat horizontal arrows, the canonical quotient comparison, finite
and coefficient-flat M, every g in K', and both independent existential lifts
are present. The canonical scalar-extension and localization maps are fixed by
actual constructions; no arbitrary map or extra comparison is assumed. The
reduction isomorphisms are in ModuleCat S or ModuleCat T, so retain the action
that would be lost by merely asking for A-linear equivalences. Reversing tensor
factors is canonical and does not change any hypothesis or conclusion. No
mismatch with the accepted node was found. Independent maintainer review of
this delivery remains required; this is not a claim of an independent agent
review.
