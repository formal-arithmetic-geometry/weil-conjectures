## Worker report

The module `Sheaf.AlgebraicGeometry.LocalFibresIntegralProjective` states Stacks
Tag 05FT as
`AlgebraicGeometry.projective_of_flat_finitePresentation_geometricallyIntegral_fibres`.
Its only proof is `sorry`; no definition or auxiliary theorem was introduced.
The node statement, dependencies and proof plan are unchanged.

Hypothesis and conclusion correspondence:

- Commutative rings and their homomorphism: `(R S : CommRingCat.{u}) [Algebra R S]`.
  The map is `algebraMap R S`; every homomorphism gives this algebra structure.
  Bundling imposes no nontriviality, Noetherianity or cardinality bound. Both rings
  can be placed in a common universe, as in the recorded approximation interface.
- Finitely presented as an algebra: `[Algebra.FinitePresentation R S]`.
  This is algebra finite presentation, not finite presentation as an R-module.
  The recorded locally-finite-presentation dependency identifies it on affine
  spectra through `LocallyOfFinitePresentation.SpecMap_iff` and
  `RingHom.FinitePresentation`.
- Flatness of the homomorphism: `(hflat : (algebraMap R S).Flat)`, using the exact
  recorded `RingHom.Flat` definition and its algebraMap equivalence.
- Every prime of R: `hfibres : ∀ p : PrimeSpectrum R, ...`; there is no restriction
  to maximal, closed, generic or inhabited spectra.
- The residue field is `p.asIdeal.ResidueField`, the ring-theoretic residue field
  at p. It is canonically isomorphic to `(Spec R).residueField p` from the recorded
  scheme-residue-field declaration; no new residue field is defined here.
- The fibre ring is `p.asIdeal.Fiber S`, the existing abbreviation
  `p.asIdeal.ResidueField ⊗[R] S`. Tensor symmetry is a canonical residue-field
  algebra isomorphism with the node's `S ⊗[R] κ(p)`; it preserves integrality
  after all field extensions.
- Geometric integrality over that residue field is precisely
  `GeometricallyIntegral (Spec.map (CommRingCat.ofHom
  (algebraMap p.asIdeal.ResidueField (p.asIdeal.Fiber S))))`.
  Its morphism is the canonical structure map, with the recorded `Spec.map`
  and `GeometricallyIntegral`, rather than an arbitrary map or an algebraic
  closure alone. The fibre encoding is verbatim the one in the recorded
  approximation theorem.
- Conclusion: `Module.Projective R S`, using the induced R-module structure.
  No finite generation as an R-module or freeness is asserted.

Dependency declarations read and used:

- `Mathlib.RingTheory.RingHom.Flat`: `RingHom.Flat` and
  `RingHom.flat_algebraMap_iff` (def-weil-pbc-flat-ring-map).
- `Mathlib.Algebra.Module.Projective`: `Module.Projective`, with its
  direct-summand definition (def-weil-pbc-projective-module).
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`:
  `AlgebraicGeometry.LocallyOfFinitePresentation` and its `SpecMap_iff`
  (def-sbc-locally-finite-presentation). This module supplies the algebra and
  ring finite-presentation API used in the signature.
- `Mathlib.AlgebraicGeometry.ResidueField`: `Scheme.residueField` and
  `Scheme.Hom.residueFieldMap` (def-weil-residue-field), read with their full
  signatures; the affine ring residue field uses the canonical ring interface.
- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Spec`, `Spec.map`
  (def-weil-affine-spectrum).
- `Mathlib.AlgebraicGeometry.Geometrically.Integral`:
  `AlgebraicGeometry.GeometricallyIntegral`
  (def-pc-geometrically-irreducible).
- `Mathlib.RingTheory.LocalRing.ResidueField.Fiber`: `Ideal.Fiber`.

Proof imports and plan: the private import
`Sheaf.AlgebraicGeometry.LocalNoetherianApproximation` supplies the recorded
`AlgebraicGeometry.exists_local_noetherian_approximation`; its signature and
complete proof docstring were read. `Mathlib.RingTheory.FiniteType` supplies
`Algebra.FiniteType.isNoetherianRing`. The already-public projectivity import
also supplies `Module.Projective.tensorProduct`. These match the three proof
steps, which are reproduced in the theorem docstring. The fourth proof node,
lem-trf-local-noetherian-fibres-projective, currently has neither a Lean record
nor a Mathlib match; it is only a proof prerequisite, so there is no statement
interface missing and no module to import for it yet.

Edge cases checked before writing:

- For the zero base ring, Spec R is empty; the fibre hypothesis is vacuous.
  A unital algebra over it is also the zero ring, whose zero module is projective.
  No `Nontrivial R` binder excludes this case.
- For a nonzero base and zero target ring, fibres are empty schemes and are not
  integral. Thus this case does not accidentally satisfy the fibre hypothesis.
- The identity map satisfies the hypotheses: residue fibres are fields and R
  is free of rank one over itself.
- Polynomial algebras have geometrically integral affine-space fibres and are
  free, often of infinite rank. Using module finite presentation would wrongly
  exclude these; the signature uses algebra finite presentation.
- No local-ring, finite-module, characteristic or Noetherian restriction occurs.

Searches made (2026-10-18):

- `msearch.py ... leansearch "A flat finitely presented algebra with geometrically
  integral fibres is projective as a module"`: eight hits, primarily
  `Module.Flat.projective_of_finitePresentation`, which requires MODULE finite
  presentation; no exact theorem.
- `msearch.py ... leanfinder "A flat finitely presented commutative algebra with
  geometrically integral fibres is projective as a module over its base"`:
  eight hits, again module-finite-presentation projectivity and unrelated
  smoothness/localization results; no exact match.
- `msearch.py ... loogle "Module.Projective, Algebra.FinitePresentation"`:
  one cotangent-module instance, no matching theorem.
- `msearch.py ... grep "GeometricallyIntegral|geometrically.*integral|fibres.*projective"
  AlgebraicGeometry`: fourteen hits, the geometric-integrality definition and
  unrelated scheme facts; no projectivity theorem.
- Direct `rg` in upstream `WeilConjectures`, side `lean/Sheaf`, and
  `dag/lean_names_upstream.json` for geometric-integrality and fibre-projectivity
  names: no exact declaration with this scheme-valued fibre hypothesis.
  `grep -rn` for the item id in upstream `WeilConjectures` gave no hits.
- The related `Algebra.projective_of_geometricallyIntegral_fibres` in
  `Sheaf.RingTheory.AffineGeometricallyIntegralProjective` was opened and read.
  Its hypothesis instead quantifies over field maps and domains of tensor
  products; its proof explicitly uses THIS node after constructing the
  scheme-interface bridge. It is a downstream consumer of this interface,
  rather than an existing declaration with the present hypothesis. Reusing
  it would reverse that proof dependency. No notion is redefined here.

Source checked: `literature/stacks-project/flat.tex`, lines 2246–2282,
lemma-fibres-irreducible-flat-projective-nonnoetherian (Tag 05FT), including its
whole proof. There is no node fault or statement dispute.

## Second reading by Q100

Independent maintainer reading of immutable delivery bf476403fd6e9eb8fa737fdd643943fe74716a68,
2026-10-18. I did not author this delivery. This replaces the worker self-check.

I read the item, all six statement-dependency records and their declarations,
Stacks flat.tex 2246–2279 (Tag 05FT, including its proof), the Noetherian lemma
at 2178–2244, and algebra.tex 11660–11669 (Tag 05DX). The delivered statement
is mathematically correct, but duplicates the already recorded base declaration.

Clause checks, for both the delivered signature and the retained existing one:

- Arbitrary commutative rings and a homomorphism: delivered `CommRingCat.{u}`
  and `[Algebra R S]`; retained independent `Type u`, `Type v`, commutative
  ring instances and `[Algebra R B]`. Every unital ring map induces this algebra.
- Finite presentation: `[Algebra.FinitePresentation R B]`, the quotient of
  finitely many polynomial variables by a finitely generated ideal, not module
  finite presentation. `RingHom.finitePresentation_algebraMap` and
  `LocallyOfFinitePresentation.SpecMap_iff` connect the recorded dependency.
- Flatness: `RingHom.Flat (algebraMap R B)` is exactly the recorded predicate;
  `flat_algebraMap_iff` identifies it with module flatness for this algebra.
- All primes: `PrimeSpectrum R` in the delivery and `Spec (.of R)` in the
  retained declaration have the same underlying prime-spectrum points.
- Residue fields and maps: `Spec.residueFieldIso` (ResidueField.lean:301)
  identifies the scheme residue field with `p.asIdeal.ResidueField`;
  `Spec.algebraMap_residueFieldIso_inv` identifies the canonical R-map.
  The retained equality involving `ΓSpecIso` and `Γevaluation` is exactly
  compatibility of `[Algebra R K]` with the specified residue-field map `ι`.
- Fibre and geometric integrality: `Ideal.Fiber` (Fiber.lean:64) is
  `κ(p) ⊗[R] B`. The canonical symmetry exchanges the tensor factors.
  `GeometricallyIntegral` and `geometrically_iff_of_commRing` quantify over all
  field base changes. Affine pullback is Spec of the tensor product, and Spec
  of a ring is integral exactly when that ring is a domain. Associativity
  identifies `(B ⊗[R] κ(p)) ⊗[κ(p)] K` with `B ⊗[R] K`, by
  `(b ⊗ a) ⊗ t ↦ b ⊗ ι(a)t`, inverse `b ⊗ t ↦ (b ⊗ 1) ⊗ t`.
  Thus the retained `hfibres` says exactly the same thing, not an extra assumption.
- Conclusion: `Module.Projective R B` is the canonical split-surjection-from-free
  definition recorded by def-weil-pbc-projective-module; no finite rank or
  freeness conclusion is added.

Universe and edge checks: any two rings can inhabit a common universe in the
original form; the existing declaration also retains independent universes.
Its test fields have universe `max u v w`, never smaller than either ring.
Taking w=0 includes an algebraic closure of each residue field in the common
universe, which detects geometric integrality; larger field extensions do not
change this criterion. No equality of distinct site universes is imposed.
Zero R forces zero B, with vacuous fibre condition and projective zero module.
For nonzero R, zero B has empty, nonintegral fibres and fails the hypothesis.
Identity maps and polynomial rings (including zero polynomial variables) are
included. Infinite module rank, all characteristics and non-Noetherian bases
are included. No extra separatedness or finiteness hypothesis appears.

Proof-plan checks: the approximation declaration has precisely the given fibre
hypothesis and returns the compatible ring pushout with R₀ finite type over Z.
The finite-type Noetherian theorem applies since Z is Noetherian. The source
Noetherian fibre lemma then gives S₀ projective. Tensor symmetry and
`Module.Projective.tensorProduct` with first factor R give projectivity after
base change; projectivity transports along the pushout module isomorphism.
The unrecorded Noetherian lemma is only a future proof prerequisite, not a
missing notion in this statement. No new helper or §1(C) correction is needed.

Findings and corrections:

- H4: the delivery replaces the parent's existing Tag 05FT binding with a
  second theorem. A different equivalent fibre presentation and a reference
  to this DAG id in the existing docstring do not warrant duplication.
  The complete replacement lean record reuses
  `Algebra.projective_of_geometricallyIntegral_fibres` and drops
  `LocalFibresIntegralProjective.lean`. This supersedes the worker's contrary
  assessment above. The item's statement and three-step source proof remain.
- H11: the original section was explicitly a worker self-check. This section
  supplies the independent clause-by-clause reading and concrete findings.

The worker records LeanSearch, LeanFinder, Loogle and direct grep searches.
I independently searched upstream WeilConjectures, side lean/Sheaf and the
upstream name index. The side search found the already-landed exact equivalent
in `AffineGeometricallyIntegralProjective.lean:61`; I read its entire signature
and docstring. The nearby Mathlib flat-projective theorem requires module
finite presentation and is not the present algebra theorem. No definitions
are introduced. Both proofs inspected are solely `sorry`; source and blueprint
docstrings are present. The delivered lean.statement is verbatim its signature;
the replacement record is verbatim the existing signature, including newlines.

Compiler evidence: prescribed scompile.py Q100 lem-trf-local-fibres-integral-projective,
run separately for the immutable delivered file and the retained existing file.
Both exited 0 with no warnings or errors. Delivered sandbox/library: 2.4/2.5 s;
retained sandbox/library: 2.3/1.8 s. Wrapper output reports private local overlays
under /dev/shm/nt-tmp and individual 60-second limits. The wrapper currently
orchestrates this through its server overlay; no direct ssh command was run.
The delivery report records compilation/preflight only in prose, so these are
fresh reproductions, not a claim to have seen a saved worker compiler log.

Route-pivot check: no item repair note exists at origin/newtargets-dag; none of
its statement or proof dependencies occurs in route-pivot-dropped.txt.
This commutative-algebra theorem introduces no dropped machinery or pro-etale
substitute. No build, landing, clone edits or branch changes were performed.
