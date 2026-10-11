## Worker report

The module `Sheaf.AlgebraicGeometry.FieldPointFactorsThroughImmersion` states
`AlgebraicGeometry.fieldPoint_factorsThrough_immersion`.  It uses Mathlib's
`Scheme`, `Scheme.Hom.residueFieldMap`, `IsImmersion`, `Spec`, and the field
instance on `Spec (.of K)`.  The first conjunct renders clause (1):
`IsIso (iota.residueFieldMap z)`.  The second conjunct renders clause (2): for
an explicitly bound field `K`, field-valued morphism `s`, and the hypothesis that
its unique point `(default : Spec (.of K))` maps to `iota.base z`, it gives exactly
one `s'` satisfying both `s' ≫ iota = s` and the point condition
`s'.base (default : Spec (.of K)) = z`.  Taking `[IsAlgClosed K]` gives the
geometric-point special case from the node (with the same field).

The dependency declarations used are Mathlib leaves: `AlgebraicGeometry.Scheme`
(def-pc-scheme), `AlgebraicGeometry.IsClosedImmersion` and
`AlgebraicGeometry.IsImmersion` (def-weil-closed-immersion),
`AlgebraicGeometry.Scheme.residueField` and
`AlgebraicGeometry.Scheme.Hom.residueFieldMap` (def-weil-residue-field),
`AlgebraicGeometry.Spec`, `Spec.map`, and `Spec.homEquiv`
(def-weil-affine-spectrum), and `AlgebraicGeometry.Scheme.SpecToEquivOfField`
(def-weil-geometric-point).  The statement deliberately uses the recorded
Mathlib notions and introduces no private definitions.

Edge cases checked: `z` is arbitrary (including empty schemes, where there is no
such point); `K` is an arbitrary field, including the prime field and the zero
point spectrum; no finite-type, separation, or algebraic-closedness hypothesis is
added.  The unique point of `Spec (.of K)` is represented by its `Unique` instance
and `default`; the geometric-point case is obtained by adding `IsAlgClosed K`.

Searches made: `msearch.py leanfinder` for field-valued morphisms through
immersions (returned `Scheme.Hom.liftCoborder`, `specTargetImageFactorization`,
and `IsImmersion.instToImage`, none an exact statement); `msearch.py loogle`
for `AlgebraicGeometry.IsImmersion, AlgebraicGeometry.Spec` (no exact match);
`msearch.py grep` for residue-field and immersion lifts in Mathlib (found only
the open-immersion residue isomorphism, closed-immersion lift requiring a kernel
condition, and preimmersion monomorphism); `rg` over `WeilConjectures` and
`lean/Sheaf` for the item and key declaration names (no existing project
statement).  The module compiled cleanly with `scompile.py`; the expected
`sorry` warning is suppressed by project options.

## Earlier second reading (a previous round; superseded)

I reread the node statement and the compiled declaration clause by clause.  The
binder `iota : Z ⟶ X` with `[IsImmersion iota]` is the stated immersion, and `z : Z`
is the chosen point; `iota.base z` is exactly `x`.  The first conjunct is the
residue-field isomorphism at that point.  The field binder and morphism `s` are
unrestricted as in the node, while the displayed equality says its unique point
maps to `x`.  The `∃!` body has both required clauses: composition with `iota`
recovers `s`, and the unique point maps to `z`.  Since `[IsAlgClosed K]` is not
needed for the factorization, the geometric-point assertion is the indicated
specialization.  No node hypothesis or conclusion was added, dropped, weakened,
or strengthened, and no statement correction was needed.

## Second reading by H1

Read the sandbox node, its source places, the delivered module, and all five
statement-dependency nodes and their actual Mathlib declarations. The Stacks
source is absent from this machine's repository literature directory; I read
its available local copy `/home/ubuntu/c1-stacks-review/schemes.tex`, at the
labels `definition-immersion`,
`definition-closed-immersion-locally-ringed-spaces`,
`lemma-restrict-map-to-opens`, `lemma-characterize-closed-subspace`,
`lemma-characterize-points` (including its preceding discussion), and
`lemma-immersions-monomorphisms`. These places assume schemes, an immersion,
and a field, without a base field, Noetherian, finiteness, separation, or
characteristic hypothesis. The locally-generated kernel condition for closed
immersions is automatic for morphisms of schemes with the stated closed
embedding and surjective stalk maps, as in the affine quotient description.

Object, hypothesis, and conclusion checklist:

- Schemes Z and X: `{Z X : Scheme.{u}}`. Mathlib `Scheme` is a locally ringed
  space locally isomorphic to affine spectra; `Scheme.Hom` is a morphism of
  the underlying locally ringed spaces. Matches `def-pc-scheme`: pass.
- Immersion iota: `(iota : Z ⟶ X) [IsImmersion iota]`.
  Read `IsImmersion` and `isImmersion_iff_exists` in
  `Mathlib.AlgebraicGeometry.Morphisms.Immersion`: its embedding, locally
  closed range and surjective stalk conditions are equivalent to exactly
  the closed-then-open factorization in `def-weil-closed-immersion`: pass.
- Chosen point z and x = iota(z): `(z : Z)` and `iota.base z`; the derived
  point x is substituted throughout rather than independently quantified:
  pass.
- Clause (1), the induced residue-field map is an isomorphism:
  `IsIso (iota.residueFieldMap z)`. Read `Scheme.residueField` (the quotient
  of the stalk by its maximal ideal) and `Scheme.Hom.residueFieldMap` (the
  map induced by the local stalk homomorphism) in `ResidueField.lean`.
  Its type is `X.residueField (iota z) ⟶ Z.residueField z`, so the direction
  and the particular induced map both match `def-weil-residue-field`:
  pass.
- Clause (2), arbitrary field and field-valued point:
  `∀ (K : Type u) [Field K] (s : Spec (.of K) ⟶ X)`.
  Read `Spec` and `Spec.map` in `Scheme.lean`, and its field-spectrum
  `Unique` instance. These give the affine scheme and its unique point
  `(default : Spec (.of K))` from `def-weil-affine-spectrum`: pass.
- Image hypothesis: `s.base (default : Spec (.of K)) = iota.base z →`.
  This is exactly the hypothesis that the point maps to x: pass.
- Existence and uniqueness of the lift:
  `∃! s' : Spec (.of K) ⟶ Z, s' ≫ iota = s ∧
  s'.base (default : Spec (.of K)) = z`.
  Composition is in Lean's diagrammatic order, hence says iota composed
  with s' is s. The point condition is present. The conjunction in the
  unique-existence predicate loses no uniqueness among other lifts:
  every lift of s has image point z because iota is injective on points
  (`IsImmersion` extends `IsPreimmersion`, an embedding). Thus the node's
  uniqueness of the morphism and its additional point clause are both
  rendered: pass.
- Geometric-point consequence, with the same algebraically closed field:
  specialize the universal field quantifier to `[IsAlgClosed K]`.
  Read `Scheme.SpecToEquivOfField` in `ResidueField.lean`: it identifies
  these morphisms with a point and a homomorphism from its residue field,
  precisely the recorded geometric-point dependency. No separate geometric
  point notion or change of coefficient field occurs. For a point in the
  image choose z and apply the displayed assertion: pass.

Edge cases: if Z is empty there is no z, so the statement is vacuous;
if X is empty no immersion from a nonempty Z has such a point. A field is
nontrivial, so Spec K has exactly one point, never zero points (the worker
report's phrase "zero point spectrum" should be read as the zero prime
ideal, not an empty spectrum). All characteristics and arbitrary fields are
covered. No index set, zero object, or integer n occurs here. Universe u is
bound and arbitrary; the common universe for schemes and K is the usual
Mathlib category `Scheme.{u}` and the same convention used by the recorded
`SpecToEquivOfField`; any set-sized data can be placed in a common ambient
universe. No accidental auto-implicit variable or extra instance is present.

Independent searches (2026-10-11):

- LeanFinder, "a field valued point of a scheme lifts uniquely along a
  locally closed embedding when its image is contained in the embedding":
  returned `Scheme.Hom.liftCoborder`, immersion characterizations,
  `IsOpenImmersion.lift_uniq`, and preimmersion embeddings. Open-immersion
  uniqueness and factorization of the immersion itself are not this theorem.
- Loogle, `AlgebraicGeometry.IsImmersion, CategoryTheory.IsIso`: returned
  `isIso_of_comp_eq_sigmaSpec`, a compact product-spectrum statement, not
  this node. An earlier unqualified `IsIso` query was rejected and replaced.
- LeanSearch, "An immersion of schemes induces an isomorphism of residue
  fields and every field valued point at its image has a unique lift":
  service unavailable (Internal Server Error); no verdict inferred from it.
- `msearch.py grep residueFieldMap`, plus direct `rg` for residue fields,
  lifts, field points and monomorphisms through Mathlib's Immersion,
  Preimmersion and ClosedImmersion modules, the project's `lean/Sheaf`,
  the source's `WeilConjectures`, and `dag/lean_names_upstream.json`.
  Read the candidate source declarations
  `Scheme.Hom.isIso_residueFieldMap` and `exists_comp_eq_of_mem_range`
  in `WeilConjectures/ConstructibleSheaf/UniversalHomeomorphism.lean`:
  they give respectively a residue isomorphism for surjective stalks
  and existence of a lift, not this node's combined unique lift at z.
  The landed `ClosedImmersionResidueFieldIso` handles only closed
  immersions and only clause (1). Mathlib's closed-immersion lift needs
  a kernel containment, its open-immersion lift handles only opens,
  and the preimmersion Mono instance gives uniqueness alone. No exact
  existing declaration was found, so the new module is retained.

Mismatches and repairs: H8, the theorem's own docstring had no source place;
added its Stacks references. H9, the standard copyright/license/author
header was missing; added the header following CompactObject.lean.
The signature and node record are unchanged and were checked verbatim
against each other. The four node proof steps are all in the docstring:
closed/open residue maps, their composite isomorphism, successive lifts,
and uniqueness with the geometric specialization. Both imports supply
notions used in the statement, all lines have at most 100 characters, and
the only proof remains `by sorry`. No definition, new node, dependency
module, hollow data, or statement correction is needed.

Validation: compiled the delivery's single module with the prescribed
`scompile.py`; then ran the prescribed `deliver2.py --no-push` preflight
before delivery.
