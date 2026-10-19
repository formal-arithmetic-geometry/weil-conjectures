## Worker report

The module `Sheaf.AlgebraicGeometry.FiniteFieldClosedSubschemeDescent` states
`WeilConjectures.FiniteFieldDatum.exists_closed_subscheme_finiteField_descent` with one
`sorry`, and defines no new notion. The source is the final paragraph of
`literature/blueprint/main-20261015/blueprint/sec-deligne-laumon-general/sk-i-dl-general-real/lem-zl-bertini-finite-cover-curve.proof.md`.
The theorem docstring records all eight proof steps of the node, including descent of the
actual inclusion and the scheme-theoretic Frobenius consequence. There is no statement
correction and no disputed clause. No maintenance repair note exists for this item.

Hypotheses and clauses, in the order of the node:

- The global finite-field datum is the binder `D : WeilConjectures.FiniteFieldDatum.{u}`.
  Its fields retain the prime `p`, positive exponent `a`, `q = p ^ a`, arbitrary base field
  of cardinality `q`, and fixed algebraic closure, with their structure map.
- The finite-type scheme over `k₀` is `X₀ : Over (Spec (CommRingCat.of D.k₀))`, with exactly
  `[LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]`. Finite type is their conjunction
  under the dependency's conventions; no separatedness or reducedness is assumed.
- The geometric fibre `X` is exactly `(D.geometricFiber X₀).left`, not another model.
  Its structure map is `(D.geometricFiber X₀).hom`.
- The fixed geometric Frobenius is `D.geometricFrobenius X₀`, the dependency's scheme
  automorphism induced by the inverse arithmetic field Frobenius.
- The given closed immersion is `(C : Scheme.{u}) (i : C ⟶ (D.geometricFiber X₀).left)`
  together with `[IsClosedImmersion i]`. These are arbitrary schemes and closed immersions.
- The positive integer is `∃ (m : ℕ) (hm : 1 ≤ m)`. Naturals with this inequality give
  exactly the positive integers; `m = 0` is excluded, `m = 1` is permitted.
- The named field `F_{q^m}` is `D.extensionSubfield m hm`. The base-field map is the
  recorded `D.extensionEmbedding m hm`, and the inclusion into `k` is its `.subtype`.
  No arbitrary intermediate field replaces this canonical subfield.
- The descended subscheme is an object `Cₘ : Over (Spec (CommRingCat.of
  (D.extensionSubfield m hm)))` and a morphism `iₘ` from it to
  `(Over.pullback (Spec.map (CommRingCat.ofHom (D.extensionEmbedding m hm)))).obj X₀`.
  Thus `iₘ` is a morphism over `F_{q^m}` into exactly `X₀ × F_{q^m}`.
  The conjunct `IsClosedImmersion iₘ.left` supplies its closed-subscheme structure.
- Equality after base change is expressed by the existential isomorphism `e` in
  `Over (Spec (CommRingCat.of D.k))`. Its source is `Over.mk
  (i ≫ (D.geometricFiber X₀).hom)`, namely `C` with its actual induced `k`-structure.
  Its target is the base change of `Cₘ` along `Spec.map` of the subfield inclusion.
  The displayed equation says that `e.hom.left`, followed by the projection to `Cₘ`,
  the descended inclusion `iₘ.left`, and the projection to `X₀`, equals `i` followed by
  the projection to `X₀`. Since `e` is over `Spec k`, the coefficient projection also
  agrees. The two projections characterize the map into the geometric fibre by its
  pullback universal property. Consequently this is exactly compatibility with the
  base-changed closed immersion under canonical base-change associativity, rather than
  just an abstract isomorphism of schemes or equality of sets of points. Conversely an
  isomorphism of the closed subschemes yields precisely this over-category isomorphism
  and projection equation. Nilpotents and the defining ideal are retained.
- The consequence is `∃ φ : Aut C, φ.hom ≫ i = i ≫ (D.geometricFrobenius X₀ ^ m).hom`.
  Lean composition reads left to right, so this is precisely `i ∘ φ = g_X^m ∘ i`.
  The same `m` governs the descended field and Frobenius power. `Aut C` is in the category
  of schemes: no erroneous requirement that `φ` be a `k`-morphism is imposed.

Dependency declarations read and used:

- `Sheaf.Paper.FiniteFieldFiber`: `WeilConjectures.FiniteFieldDatum`,
  `.extensionSubfield`, `.extensionEmbedding`, `.geometricFiber`. Read both the local
  module and the live source via `scompile.py --source Sheaf.Paper.FiniteFieldFiber`.
  The module is imported transitively by the public Frobenius import.
- `Sheaf.AlgebraicGeometry.FrobeniusDetailed`:
  `WeilConjectures.FiniteFieldDatum.geometricFrobenius`; read its construction, inverse,
  `galoisMap`, and projection and affine characterizations in full. Publicly imported.
- `def-weil-scheme-morphism-properties` is explicitly a convention collection with no
  declaration. Its named finite-type and closed-immersion notions use Mathlib's
  `AlgebraicGeometry.LocallyOfFiniteType`, `AlgebraicGeometry.QuasiCompact`, and
  `AlgebraicGeometry.IsClosedImmersion`, in `Morphisms.FiniteType`,
  `Morphisms.QuasiCompact`, and `Morphisms.ClosedImmersion` respectively. Their class
  signatures and docstrings were read; the closed-immersion module is publicly imported.
- `def-pc-base-change` explicitly records `CategoryTheory.Over.pullback`,
  `CategoryTheory.Limits.pullback.fst` and `.snd` for scheme base change, distinct from
  its primary module-base-change declaration. These are the constructions used here.
  Read the complete live `WeilConjectures.AlgebraicGeometry.BaseChangeConventions` via
  `scompile.py --source`, and Mathlib's `CategoryTheory.Comma.Over.Pullback` definition
  and `pullbackComp`. The finite-field dependency already imports the matching side
  base-change-conventions module; importing the separately published upstream copy as
  well would risk duplicate declarations, so that additional import is omitted under
  the dispatcher's duplicate-module guidance. No duplicate definition is introduced.

The available non-Mathlib proof prerequisites are imported without `public`:
`Sheaf.AlgebraicGeometry.LimitAffineTransition` and
`WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit`. The latter includes the
recorded spreading-out and eventual closed-immersion theorems and the Mathlib Noetherian,
finite-presentation and quasi-separatedness modules. The unique-subfield theorem and
base-change conventions already enter through the statement dependency. Thus the proof
plan's dependencies remain available without new declarations or import cycles.

Edge cases checked: the empty ambient scheme and empty closed subscheme are admitted;
the identity immersion is admitted; nonreduced closed subschemes retain their scheme
structure through an actual isomorphism; no smoothness, connectedness, affineness,
properness or separatedness assumption is added. Any prime and any positive exponent in
the finite-field datum are admitted, including characteristic two. The closure is not
replaced by a specially chosen algebraic-closure type. The single explicit universe `u`
is the universe of the recorded datum and its geometric-fibre API, and can be arbitrarily
large. There are no auto-bound variables or file-local definitions or notation.

Searches performed with `msearch.py Q150 lem-zl-bertini-finite-field-descent`:

- LeanFinder: `A closed subscheme of a finite type scheme over an algebraic closure of a
  finite field descends to a finite extension with a power of geometric Frobenius acting
  on it`. Eight hits: finite global-section algebras, arithmetic Frobenius at prime
  ideals, finite fibres, and proper Proj; none is the closed-subscheme descent assertion.
- Loogle: `AlgebraicGeometry.IsClosedImmersion, CategoryTheory.Limits.pullback`.
  Six hits: preservation of closed immersions under pullback, closed diagonal lifts and
  ideal-sheaf kernel base change; no finite-constant-field descent theorem.
- LeanSearch: `closed subscheme over algebraic closure of finite field descends to finite
  extension`. Eight hits: universally-closed descent, closed-immersion characterizations,
  closed-immersion base-change stability, ideal-sheaf subschemes and implications to
  finite/integral/immersion/universally-closed; no matching theorem.
- Mathlib grep through msearch: `descend|finite.?field` in `AlgebraicGeometry`.
  Twenty-three hits: effective epimorphisms, general affine-transition limits and flat
  descent. None gives this finite-field statement and its Frobenius consequence.
- Direct `rg` in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` and
  `/home/ubuntu/weil-newtargets-shared/lean/Sheaf` for
  `lem-zl-bertini-finite-field-descent|finite.field.descent|descend.*[Ss]ubscheme|closed.*[Ff]robenius`.
  Only unrelated closed-point Frobenius and coherent/condensed-sheaf descent results.
  A separate literal item-id search in upstream returned no match.
- Direct `rg` for `exists_closed_subscheme_finiteField_descent` in the upstream name
  index, the source project and `lean/Sheaf` returned no match. This declaration is new.

Validation: the prescribed `scompile.py Q150 lem-zl-bertini-finite-field-descent <file>`
compiled both the sandbox and final module paths successfully, with no errors and no
unexpected warnings (13.4 and 12.9 seconds respectively). The node copy changes only
`lean`; its signature is copied verbatim from the theorem, and its date is from UTC.
The source file has no line over 100 characters.

## Second reading by Q150

Author's second reading, not an independent review; the maintainer supplies the independent
review under this dispatch protocol. Reopened the node and reread the complete theorem.
The finite-type conditions, exact geometric fibre and Frobenius are the recorded ones.
Checked that the isomorphism is over `Spec k`, rather than an unstructured scheme
isomorphism: this supplies the necessary second projection equation. Checked that the
explicit first-projection equation goes all the way to `X₀`, so it determines the actual
base-changed embedding into `X`, not merely its topological image. The descended inclusion
is over `F_{q^m}` and is explicitly closed. Verified that its exponent and the exponent in
the automorphism clause are the same positive `m`, and that composition has the node's
orientation. The automorphism has no `k`-linearity restriction. No mismatch or statement
change was found; no dependency repair or new definition node is needed.
