## Worker report

The module `Sheaf.RingTheory.ArtinianFiniteTypeResidueCriterion` states both clauses
of `lem-sfb-artinian-finite-type-residue-criterion`, with two named theorems and
`sorry` proofs only. It introduces no definitions. The node changes only in `lean`.

Clause-by-clause correspondence:

- Commutative rings `R` and `A`: `[CommRing R] [CommRing A]`.
- The given homomorphism `R → A`: `(f : R →+* A)`. There is no injectivity,
  surjectivity, locality, field-base, or Noetherian-base hypothesis.
- Artinian target: `[IsArtinianRing A]`, Mathlib's descending-chain condition on
  submodules of the regular module, hence on ideals in this commutative setting.
- Local target with its unique maximal ideal: `[IsLocalRing A]`. This class includes
  `Nontrivial A`, agreeing with the existence of a maximal ideal.
- The field `k = A/m`: `IsLocalRing.ResidueField A`, definitionally the quotient by
  `IsLocalRing.maximalIdeal A`; Mathlib supplies its `Field` instance. The displayed
  signatures name its canonical quotient homomorphism `IsLocalRing.residue A`.
- Finite generation of `A` over `R`: `f.FiniteType`.
- Finite generation of `k` over `R` with the specified induced structure:
  `((IsLocalRing.residue A).comp f).FiniteType`. Both directions are stated by `↔`
  in `RingHom.finiteType_iff_residue_of_isArtinianRing`.
- The two affine structure morphisms: respectively
  `AlgebraicGeometry.Spec.map (CommRingCat.ofHom f)` and
  `AlgebraicGeometry.Spec.map (CommRingCat.ofHom ((IsLocalRing.residue A).comp f))`.
  Contravariance gives exactly `Spec A → Spec R` and `Spec k → Spec R`.
- Each scheme morphism is of finite type: the conjunction of
  `AlgebraicGeometry.LocallyOfFiniteType` and `AlgebraicGeometry.QuasiCompact` on
  that same morphism. The second theorem is the equivalence between these two
  conjunctions, retaining both halves of the node's scheme-theoretic clause.

Universes are explicit and `autoImplicit` is false. The algebraic theorem uses
independent `u v`. The scheme theorem uses `R A : Type u`, the universe convention
of Mathlib's `Spec.map` and scheme-morphism properties. This allows any common
universe and does not impose a cardinal bound; rings can always be regarded in
one common universe. There are no quantified test objects or index types.

Dependency declarations read and used:

- `def-weil-field`: `Field`, `Mathlib.Algebra.Field.Defs`, used through the
  canonical `IsLocalRing.ResidueField.field` instance. The residue-field definition,
  field instance and quotient map are in `Mathlib.RingTheory.LocalRing.ResidueField.Defs`.
- `def-weil-pbc-finite-type-algebra`: `RingHom.FiniteType`,
  `Mathlib.RingTheory.FiniteType`; its body uses `Algebra.FiniteType` with precisely
  `f.toAlgebra`, so no arbitrary or incompatible algebra structure is introduced.
- `def-weil-affine-spectrum`: `AlgebraicGeometry.Spec` and
  `AlgebraicGeometry.Spec.map`, `Mathlib.AlgebraicGeometry.Scheme`.
- `def-weil-finite-type-morphism`: `AlgebraicGeometry.LocallyOfFiniteType`,
  `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`, and `AlgebraicGeometry.QuasiCompact`,
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`. Their conjunction is exactly
  the existing dependency record's finite-type convention.

All stated proof dependencies are imported without `public` unless their modules
are already public statement dependencies:

- `IsSemiprimaryRing.finite_of_isArtinian`, `Mathlib.RingTheory.HopkinsLevitzki`
  (the Artinian finite-over-residue-finite lemma).
- `AlgebraicGeometry.locallyOfFiniteType_iff`,
  `Mathlib.AlgebraicGeometry.Morphisms.FiniteType` (all affine pairs).
- `AlgebraicGeometry.HasRingHomProperty.iff_exists_appLE`,
  `Mathlib.AlgebraicGeometry.Morphisms.RingHomProperties` (pointwise criterion).
- `IsArtinianRing.isMaximal_of_isPrime`, `Mathlib.RingTheory.Artinian.Module`, and
  `IsLocalRing.eq_maximalIdeal`, `Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic`
  (unique prime). No proof-dependency import cycle arises.

Each theorem docstring contains its complete natural-language proof plan,
including the generator-lifting argument, finiteness over the polynomial image
using the recorded Artinian finiteness lemma, and the singleton-spectrum argument.
The cited source was read locally: Stacks `algebra.tex`,
`lemma-essentially-of-finite-type-into-artinian-local`, Tag 07DT (2), and
`morphisms.tex`, `lemma-artinian-finite-type`, Tag 02HV. The latter is specialized
here to its affine target exactly as the node states. The current blueprint
`sk-thm-sf-ctf-stability-direct-images.proof.md` (3) was also read for context.

Edge cases checked mathematically before writing:

- `A` is already a field: its maximal ideal is zero, giving the same criterion
  under the canonical quotient isomorphism.
- Zero algebra generators: a surjection from `R` onto the residue field is
  allowed; the converse still adjoins finitely many module generators.
- Nilpotents: both `Z/p²` and dual numbers over a field meet the hypotheses; no
  reducedness hypothesis has been introduced.
- Arbitrary non-Noetherian base: nothing in the statement or source requires it
  to be Noetherian. The finite-over-polynomial-image argument remains applicable.
- `Z → Q[ε]/(ε²)`: the residue field `Q` is not finite type over `Z`, and neither
  is the target, agreeing with the equivalence.
- The zero ring is excluded by localness, as it must be because the node requires
  a unique maximal ideal and a residue field. A zero source cannot map unitaly
  into the nontrivial target, and no extra exclusion is necessary.
- Both spectra are singletons. An affine-open inverse image can be empty; the
  docstring explicitly includes the empty and singleton compactness cases.

Searches for an exact existing statement:

- `msearch.py`, LeanFinder query: "An Artinian local algebra is of finite type over
  a ring if and only if its residue field is of finite type". Eight hits, including
  `Algebra.QuasiFinite.iff_of_isArtinianRing`, residue-field module-finiteness
  results, and `Module.finite_of_isArtinianRing`. None states this criterion:
  the quasi-finite result has an Artinian base, and the Jacobson result assumes
  finite type already and an additional Jacobson-base condition.
- `msearch.py`, Loogle query: `IsArtinianRing, RingHom.FiniteType`. Zero hits.
- `msearch.py`, grep query:
  `finiteType.*residue|finiteType.*residue|finiteType.*artinian|finiteType.*Artinian`
  in `RingTheory`. Nine hits; these concern essential finite type or quasi-finite
  fibres, not the required ordinary finite-type equivalence.
- Direct `rg` in `lean/WeilConjectures` and `lean/Sheaf` for
  `finiteType.*[Rr]esidue|finiteType.*[Aa]rtinian|finite_type.*[Rr]esidue|FiniteType.*ResidueField`.
  Hits use finite type on residues, or give different theorems such as isolated
  primes over fields; none gives the Artinian-local iff over an arbitrary base.
  The isolated-prime statement's full signature and docstring were read.
- Direct node-id search in `lean/WeilConjectures`: no hits.
- Direct search of Mathlib, both project trees and `dag/lean_names_upstream.json`
  for the chosen declaration names: no clashes.

Validation: `scompile.py Q70 lem-sfb-artinian-finite-type-residue-criterion` compiled
both the sandbox module and its intended library module cleanly. An initial
unknown `QuasiCompact` identifier was repaired by importing its owning module
publicly. The final sources contain no diagnostic commands or extra proofs.

No statement dispute, correction, new node, or dependency interface repair is needed.

## Second reading by Q70

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
