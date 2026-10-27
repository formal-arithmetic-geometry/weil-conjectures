## Worker report

The module `Sheaf.RingTheory.BoundedPseudoCoherentStalkwisePerfect` states
`DerivedCategory.isPerfectRingComplex_of_boundedBelow_pseudoCoherent_stalkwisePerfect`.
Its only theorem has proof `sorry`; no definitions or proofs are added.

Source checked directly: literature/stacks-project/more-algebra.tex,
lemma-check-perfect-stalks (Tag 068W), lines 20063–20133. The final paragraph proves
(2) implies (1) under cohomological boundedness below. The node is unchanged.
The source uses ordinary localization, which is flat and therefore agrees with
the derived scalar extension used by the node and the Lean statement.

Hypotheses and clauses, in order:

- Any commutative ring B: `{B : Type u} [CommRing B]`. There is no Noetherian,
  domain, local, nontrivial or nonempty-spectrum assumption.
- K in D(B): `(K : DerivedCategory (ModuleCat.{u} B))` with
  `[HasDerivedCategory.{w} (ModuleCat.{u} B)]`. The latter is the recorded
  localization-size convention, not a mathematical ring hypothesis.
- Pseudo-coherent: `(hK : IsPseudoCoherent K)`. The recorded definition supplies
  a bounded-above complex with finite free terms and an isomorphism in D(B).
- Some integer c with H^i(K)=0 for i<c: `hbounded` is exactly
  `∃ c : ℤ, ∀ i : ℤ, i < c → IsZero ((homologyFunctor (ModuleCat.{u} B) i).obj K)`.
  This is cohomological boundedness, without requiring K itself to be a strictly
  bounded representative and without any prescribed value of c.
- Each prime ideal q: `∀ q : PrimeSpectrum B` packages exactly an ideal and
  its primality. Its localization is the recorded `Localization.AtPrime q.asIdeal`.
  This quotient localization is in the same universe u as B.
- K_q = K tensor-derived B_q by K-flat resolutions: the expression in `hlocal`
  chooses the universal fixed-second-factor functor from
  `exists_derivedTensor_second_factor_functor (algebraMap B (Localization.AtPrime
  q.asIdeal))`, evaluates it at `HomologicalComplex.single ... 0` of the regular
  localized module, then evaluates the resulting functor at K. This is exactly
  the coefficient convention used by `DerivedCategory.IsPerfect.scalarExtension`.
  The theorem characterizes the functor by its left-derived universal property
  and computes it on K-flat resolutions; this is not a choice of arbitrary maps
  or of objects merely known to exist.
- Perfectness for every q: `hlocal` applies `IsPerfectRingComplex` over the
  localized ring to the preceding derived object. Its bounded finite-projective
  representative and both bounds are existentially quantified INSIDE each q.
  No uniform bound is required.
- Conclusion K perfect over B: `IsPerfectRingComplex K`. Unfolding the recorded
  predicate gives a cochain complex P, integers a,b, strict vanishing below a and
  above b, finite projective terms, and `Nonempty (K ≅ Q.obj P)`.
- Both derived localization universes are explicit and independent (`w`, `wq`).
  The family of target `HasDerivedCategory` instances only chooses the target
  localizations needed to type scalar extension; it imposes no equality with u
  or with the source localization universe.

Statement dependency declarations read with their definitions/docstrings:

- Mathlib.Algebra.Homology.DerivedCategory.Basic: `DerivedCategory`,
  `HasDerivedCategory`, `DerivedCategory.Q`.
- WeilConjectures.RingTheory.RingPseudoCoherent:
  `DerivedCategory.IsPseudoCoherent`.
- Mathlib.RingTheory.Localization.AtPrime.Basic: `Localization.AtPrime`.
- WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat:
  `CategoryTheory.MorphismProperty.kFlat` (used by the fixed-second-factor interface).
- Sheaf.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral:
  `DerivedCategory.IsPerfectRingComplex` (the recorded independent-universe definition).
- Sheaf.Algebra.Homology.DerivedTensorSecondFactorFunctor:
  `DerivedCategory.exists_derivedTensor_second_factor_functor`.
  Its existing DAG node is added to stmt_deps, since scalar extension appears in
  the statement. It was already a proof dependency. No dependency record is repaired.
- Cohomology uses `DerivedCategory.homologyFunctor`, read in Mathlib's
  Algebra/Homology/DerivedCategory/HomologySequence.lean, exposed by the imports.

Proof-only imports retain the stated proof dependencies:
WeilConjectures.Algebra.Homology.BoundedFlatKFlat,
Sheaf.CategoryTheory.DerivedCategory.PerfectScalarExtension,
Mathlib.RingTheory.Spectrum.Prime.Topology (the Mathlib match for the spectrum
quasi-compactness/unit-ideal node), and Sheaf.RingTheory.PerfectPrincipalCoverGlue.
`lem-sfb-bounded-pseudocoherent-residue-model` has no Lean record/module in the
read checkout, so no import can yet be added for it. Its role is recorded explicitly
in step 3 of the theorem docstring; it is not needed to type this statement.
The docstring includes all four proof steps and all their dependency node names.

Edge cases checked before writing: B=0 has empty prime spectrum, so `hlocal` is
vacuous, and the conclusion correctly holds since all B-modules are zero. The
proof plan uses the empty finite cover in this case. K=0 is permitted with any
cohomological lower bound. Bounds c, a and b range over all integers, so negative
and zero bounds are included. No order constraint a≤b is added to the recorded
perfect predicate (the zero object may have an empty support interval). A field
has the single zero prime, whose localization yields the expected hypothesis.
No uniform bound on primewise perfect models or residue models is assumed.
The source and target module universes coincide with the coefficient-ring universe
as required by the recorded ring-perfect predicate, while derived morphism
universes are independent.

Searches (2026-10-24), using the prescribed msearch.py wrapper:

- leanfinder: "A bounded below pseudo coherent complex is perfect if every prime
  localization is perfect". Eight hits: cohomological IsGE/IsLE support and
  representative lemmas, not this perfection criterion.
- leansearch: "A pseudo coherent complex bounded below is perfect if its prime
  localizations are perfect". Eight hits: prime localization, Frobenius/topological
  perfection, finite presentation and bounded representatives; no matching criterion.
- loogle: "DerivedCategory.IsPerfectRingComplex, DerivedCategory.IsPseudoCoherent".
  Zero hits; IsPerfectRingComplex is not a Mathlib identifier.
- grep: "pseudo.?coherent|perfect.*stalk|perfect.*localiz|localiz.*perfect".
  One Mathlib hit about PerfectField, unrelated to perfect complexes.
- rg searched lean/WeilConjectures and lean/Sheaf for perfect/stalk/localization
  combinations, and narrowed the search to RingTheory and CategoryTheory/DerivedCategory
  for pseudo-coherent/perfect and local perfection criteria. Existing
  PseudoCoherentMaximalFibrePerfect requires uniform Tor-amplitude bounds and is
  different; principal-cover gluing and finite-Tor perfection are inputs, not this
  statement. No exact existing statement was found.
- grep -rn of this node id in lean/WeilConjectures found no declaration.
- rg of the proposed full declaration name in both Lean roots and
  dag/lean_names_upstream.json found no collision.

The supplied CompactObject example is withdrawn in the current checkout. I read
its current node record and the upstream module
WeilConjectures.CategoryTheory.CompactObject instead, retaining the prescribed
module/public-import/expose/docstring conventions.

No new nodes, dependency modules, statement corrections, disputed statements or
hollow definitions. Single-file scompile.py validation succeeded for both the
sandbox and library module modes, with no errors or warnings.


## Second reading by Q85

The delivered section under this heading was a self-audit ("not an independent review";
delivery-errors H11). It is replaced by the independent reading of the maintainer's
reviewer, made with the node, Stacks more-algebra.tex lines 20064-20133 (Tag 068W,
lemma-check-perfect-stalks) and the Lean module open.

Node clause by clause, with its Lean and the verdict:

- Any commutative ring B, no Noetherian hypothesis: `{B : Type u} [CommRing B]`; no other
  ring instance. OK.
- K in D(B) [def-weil-abstract-derived-category]:
  `K : DerivedCategory (ModuleCat.{u} B)` with `[HasDerivedCategory.{w} ...]`, the size
  convention of the recorded definition (Mathlib, existing). OK.
- K pseudo-coherent [def-pc-ring-pseudo-coherent-complex]: `hK : IsPseudoCoherent K`; the
  recorded def (WeilConjectures.RingTheory.RingPseudoCoherent) is
  `∃ E b, E.IsStrictlyLE b ∧ (∀ j, Free ∧ Finite) ∧ Nonempty (Q.obj E ≅ K)`, i.e. a
  bounded-above finite-free model. OK.
- Some integer c with H^i(K)=0 for i<c (the "bounded below" of 068W, "Say H^i(K)=0 for
  i<a"): `hbounded : ∃ c, ∀ i < c, IsZero ((homologyFunctor _ i).obj K)`. Cohomological,
  as in the source, c existential. OK.
- Every prime q, B_q [def-weil-pbc-localization-at-prime]: `∀ q : PrimeSpectrum B` and
  `Localization.AtPrime q.asIdeal` (the recorded Mathlib declaration, existing). OK.
- K_q = K ⊗^L_B B_q by K-flat resolutions [def-pc-module-kflat-complex]: the functor `T`
  of `exists_derivedTensor_second_factor_functor (algebraMap B B_q)` (node
  lem-pc-derived-tensor-second-factor-functor) at the single complex B_q[0], applied to K.
  `T.obj N` is the left derived functor of Tot(- ⊗_B N) with respect to quasi-isomorphisms,
  computed on K-flat models; it is unique up to unique isomorphism, and
  `IsPerfectRingComplex` is invariant under isomorphism, so the `Classical.choose` does
  not matter. It is the same scalar extension as the landed
  `IsPerfect.scalarExtension` (lem-sc-perfect-pullback-perfect-residue, used in step 2).
  OK.
- K_q perfect over B_q for every q, bounds not uniform: `hlocal : ∀ q, IsPerfectRingComplex
  (...)`; the representative and its bounds a, b are quantified inside the definition, so
  inside each q. OK, no uniformity added.
- Conclusion K perfect [def-pc-perfect-ring-complex]: `IsPerfectRingComplex K`, the
  recorded def `∃ P a b, P.IsStrictlyGE a ∧ P.IsStrictlyLE b ∧ (∀ i, Projective ∧ Finite)
  ∧ Nonempty (C ≅ Q.obj P)`: bounded complex of finite projective modules. OK.

Statement dependency on the theorem node lem-pc-derived-tensor-second-factor-functor: the
item uses the functor that this theorem constructs (`Classical.choose (...).2`); no
definition node owns a derived scalar extension of ordinary modules with a declaration
(sk-def-sfb-derived-extension-of-scalars is a unit for ring objects of a Grothendieck
category, realized by nothing for ModuleCat), and the landed sibling
lem-sc-perfect-pullback-perfect-residue has the same stmt_dep for the same object. The
statement genuinely depends on the object the theorem constructs: accepted.

Universes: B, its modules and B_q in u (the recorded perfect predicate needs the
coefficient ring and module universes equal); derived hom universes w, wq independent.
No variable left unbound (`autoImplicit false`; `universe u w wq`).

Edge cases: B = 0 (Spec empty, `hlocal` vacuous, K = 0 is perfect: the statement is true,
the proof's empty cover r = 0 is allowed by the glue lemma); K = 0; c, a, b any integers;
a field (single prime, B_q = B up to the localization map).

Searches: rg in side-live lean/Sheaf and lean/WeilConjectures for `AtPrime` together with
`IsPerfect`, and for `068W`: hits are UniformPerfectQuotientBound (uniform bounds),
Perfect/FiniteFree (finite-free models), and the 069C applications
AffinePolynomialResolutionOfStalkwise / AffineSectionsFiniteTorOfStalkwise, which use 068W
in their proofs but do not state it. lem-weil-pbc-pseudocoherent-maximal-fibre-perfect
(068V) needs a uniform amplitude. No existing statement.

Records: only the item node changed against the base, in `lean` and by adding the
stmt_dep lem-pc-derived-tensor-second-factor-functor; `lean.statement` is verbatim the
file's signature. Module and declaration docstrings carry Tag 068W and
`(blueprint: lem-sfb-bounded-pseudocoherent-stalkwise-perfect)`; the declaration
docstring has the four proof steps. Proof is `sorry`; no definitions. Lines ≤ 100.
Plain imports are the modules of the proof_deps (bounded-flat K-flat, perfect scalar
extension, Spec quasi-compactness, principal-cover glue).

Mismatches found: none in the Lean or the node. Changed: this section only.
