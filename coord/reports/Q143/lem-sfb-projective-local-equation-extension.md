## Worker report

The module `Sheaf.AlgebraicGeometry.ProjectiveLocalEquationExtension` states
`AlgebraicGeometry.projective_local_equation_extension`, with its sole theorem proof
`sorry`. The item is unchanged except for `lean`. There are no new nodes or dependency
repairs, no statement correction, and no disputed statement.

Source read: `literature/stacks-project/constructions.tex`, Tag 03GL,
`lemma-closed-in-projective-space`, especially the converse inclusion J ⊆ J′
(lines 3025–3055). The source homogenizes f, clears its vanishing after localization
on each other chart, and takes the maximum exponent. The declaration docstring
records all five DAG proof steps and their dependencies.

The correspondence with every hypothesis and conclusion is as follows.

- An arbitrary commutative ring is `(R : Type u) [CommRing R]`. There is no field,
  domain, nontriviality, reducedness, Noetherianity or finite presentation assumption.
- The nonnegative dimension is `n : ℕ`; all coordinates, including the fixed `a`,
  are indexed by `Fin (n + 1)`.
- B is Mathlib's `MvPolynomial (Fin (n + 1)) R`. The total-degree components are
  `homogeneousSubmodule (Fin (n + 1)) R`, and the canonical degree-one grading is
  `MvPolynomial.gradedAlgebra`. The grading instance is supplied explicitly to
  every graded construction, avoiding both additional assumptions and local or
  global instance registrations.
- P is exactly `AlgebraicGeometry.Proj` of those components, the recorded match
  for `def-pc-proj`. The morphism binder `i : Z ⟶ Proj ...` and the instance
  `[IsClosedImmersion i]` state the arbitrary closed immersion.
- U_j is `Proj.basicOpen ... (X j)`; A_j is
  `HomogeneousLocalization.Away ... (X j)`, the recorded declaration for
  `def-nagata-homogeneous-localization-degree-zero`.
- Z_j is the inverse-image open implicit in the codomain of `i.app U_j`:
  Mathlib's signature is `Γ(P,U_j) ⟶ Γ(Z,i ⁻¹ᵁ U_j)`.
  Its section ring includes nilpotents and is the zero ring on an empty open.
- The map A_j → Γ(Z_j,O_Z) is the canonical `Proj.awayToSection ... (X j)`
  followed by `i.app U_j`. Hence `hf : i.app U_a (Proj.awayToSection ... f) = 0`
  is precisely `f ∈ J_a`, the kernel condition. No arbitrary chart map is supplied.
  `Proj.basicOpenIsoAway` identifies this same canonical map from A_j to
  Γ(P,U_j) as an isomorphism because `isHomogeneous_X R j` has positive degree one.
- The witnesses `∃ (d N : ℕ) (F : homogeneousSubmodule ... d)` are exactly
  d,N ≥ 0 and a homogeneous degree-d polynomial. Zero polynomials are allowed
  in every homogeneous component, so degree is not erroneously forced to be
  the total degree of a nonzero polynomial.
- The first conjunct uses `HomogeneousLocalization.Away.mk` with denominator
  exponent d and numerator F, stating f = F / z_a^d in A_a.
- The middle conjunct quantifies over every `j : Fin (n + 1)`. Its fraction is
  `Away.mk ... (d + N) (X a ^ N * F) ...`, exactly z_a^N F / z_j^(d+N).
  Applying the same canonical map and equating its value to zero states actual
  section vanishing on Z_j. The proof argument certifies homogeneity of the
  product using existing `isHomogeneous_X_pow` and `IsHomogeneous.mul`; it adds
  no hypothesis or auxiliary theorem.
- The last conjunct states f = (z_a^N F)/z_a^(d+N) in A_a, including explicitly
  the node's final "in particular" clause, using the identical d,N,F witnesses.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Scheme`:
  `AlgebraicGeometry.Proj` and `AlgebraicGeometry.projIsoSpec`;
  `Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Topology`:
  `ProjectiveSpectrum.basicOpen`. These are the recorded `def-pc-proj` matches.
  `Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic` publicly supplies these
  and `Proj.basicOpen`, `Proj.awayToSection`, and `Proj.basicOpenIsoAway`.
- `Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization`:
  `HomogeneousLocalization.Away`, `Away.mk`, `Away.mk_surjective` and `Away.val_mk`.
  The constructor's signature and docstring identify its fraction as x/f^n.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`:
  `AlgebraicGeometry.IsClosedImmersion`, a closed embedding with surjective stalk maps.
- Proof dependencies remain Mathlib matches: `Localization.Away`
  (`Mathlib.GroupTheory.MonoidLocalization.Away`, with the ring localization API
  in `Mathlib.RingTheory.Localization.Away.Basic`);
  `Scheme.IdealSheafData`, `IdealSheafData.subschemeι` and
  `IsAffineOpen.isLocalization_basicOpen` (IdealSheaf.Basic/Subscheme and AffineScheme);
  `AlgebraicGeometry.ΓSpec.adjunction` (`Mathlib.AlgebraicGeometry.GammaSpecAdjunction`);
  and `Proj.awayι_preimage_basicOpen` (`Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic`).
  Imports for proof-only modules are plain imports; statement modules are public imports.

Edge cases checked before writing: f = 0 allows d = 0,F = 0,N = 0;
n = 0 has a single chart and permits N = 0; Z empty and any empty inverse-image
chart give the zero section ring; the zero base ring is allowed; Z = P forces
f = 0 through the canonical chart-section isomorphism; rings and closed subschemes
with nilpotents are covered because equality is tested in their section rings.
No chart is assumed inhabited, and no quotient is replaced by its radical.
The common universe `u` is the ordinary Mathlib `Scheme.{u}` convention for the
base ring, polynomial Proj and morphisms, without a restriction to universe zero.

Searches for an existing statement:

- `msearch.py ... leanfinder`: "A local equation of a closed subscheme of projective
  space extends to a homogeneous equation on every chart after multiplication by
  a power of its chart coordinate". Eight hits: ProjIsoSpecTopComponent fraction
  membership and carrier lemmas, StructureSheaf.IsFraction, sectionInBasicOpen,
  and Proj.mk_mem_toSpec_base_apply. They construct/localize chart sections or
  test point membership; none asserts this extension with section vanishing.
- `msearch.py ... leansearch`: "A local equation on a closed subscheme of projective
  space extends to a homogeneous polynomial after multiplying by a coordinate power".
  Eight hits: Polynomial.homogenize, Proj.homOfLE_toBasicOpenOfGlobalSections_ι,
  StructureSheaf.IsFraction, Proj.mk_mem_toSpec_base_apply,
  Proj.fromOfGlobalSections_resLE, SectionSubring.mul_mem',
  Proj.openCoverOfMapIrrelevantEqTop and Proj.basicOpenIsoSpec. None is the theorem.
- `msearch.py ... loogle '"Proj", "vanish"'`: twelve hits concerning
  `ProjectiveSpectrum.vanishingIdeal` and its zero locus. Those intersect prime
  ideals and lose the nilpotent information expressly required here.
- `msearch.py ... grep 'homogeniz|homogenis|vanish.*[Pp]roj|[Pp]roj.*vanish'`:
  eighteen hits, mainly the same pointwise vanishing ideal and univariate
  Polynomial.homogenize. No exact match.
- `rg` of `lean/WeilConjectures` and `lean/Sheaf`, both by item id and by the
  prospective theorem names, found no matching declaration. Broader searches
  for projective equations, homogeneous equations and coordinate powers found
  existing chart and Hilbert-coordinate constructions, but no such theorem.
  Focused `rg 'homogeniz|homogenis|projective_local_equation_extension|projectiveLocalEquationExtension'`
  of both AlgebraicGeometry trees found dehomogenization utilities and Hilbert
  equation definitions only. The name was also checked in `dag/lean_names_upstream.json`.
  The exact wrapper search outputs are retained in `searches.jsonl` in this sandbox.

Validation: the prescribed `scompile.py` checked the module both as a sandbox file
and at its library module path, cleanly. Initial probes exposed the lack of a global
polynomial grading instance; the final signature passes Mathlib's canonical grading
explicitly. A superfluous `simpa` warning was removed. No build was run directly.

## Second reading by Q143

I reread the original node, its three statement dependencies and their recorded
signatures, the Stacks converse paragraph, and the completed theorem. This is a
separate self-review pass; no other agent was started, as the dispatch brief prohibits it.
The arbitrary CommRing R, n : ℕ, Fin(n+1) coordinates, actual polynomial Proj,
closed immersion i, canonical homogeneous chart ring, and kernel hypothesis hf
match the objects and hypotheses exactly. The three conjuncts respectively match
the unmultiplied fraction identity, vanishing of the multiplied fraction on every
closed-subscheme chart, and the final identity on chart a. F is a genuine element
of the degree-d submodule. The section maps target the actual inverse-image opens,
so no radical or residue-field test is substituted. Empty charts, f = 0, n = 0,
the zero ring and nonreduced Z remain admitted. No mathematical mismatch or node
fault was found. The implementation change from the first pass was to pass the
canonical grading explicitly at each use, so the signature is self-contained
outside this module and does not register an instance. There are no new nodes,
helper definitions or dependency repairs to review.
