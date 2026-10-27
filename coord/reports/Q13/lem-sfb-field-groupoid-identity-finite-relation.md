## Worker report

The module `Sheaf.AlgebraicGeometry.FieldGroupoidIdentityFiniteRelation` states
`AlgebraicGeometry.AlgebraicSpace.fieldGroupoid_identity_finite_relation`, with `sorry`.
No definitions or additional theorems are introduced. The node statement is unchanged;
`stmt_deps` gains the already landed `def-sfb-algebraic-space-groupoid`, whose presheaf
interface states the algebraic-space groupoid in the hypothesis. No statement correction
or disputed statement is needed.

Source read: `literature/stacks-project/stacks-morphisms.tex:4193` (Tag 06N0,
lemma-DM-residual-gerbe), first proof paragraph and the following parenthetical verification;
`spaces-over-fields.tex:1269` (Tag 06LZ, lemma-locally-finite-type-dim-zero);
`varieties.tex:3736` (Tag 06LH, lemma-algebraic-scheme-dim-0). The relative-S formulation is
retained: products of presheaves on `Over S` represent the relative products over S.

Hypotheses, clause by clause:

- `S : Scheme.{u}` is arbitrary. `K : Type u` with `[Field K]` is the field. `b : Spec K ⟶ S`
  specifies its arbitrary S-structure; no property of S is imposed.
- `R : AlgebraicSpace S` uses the recorded full-subcategory definition. Its underlying
  presheaf is `R.obj.obj`, and U is `yoneda.obj (Over.mk b)`.
- `s,t,e,i,c` are the natural transformations with precisely the indicated source, target,
  unit, inverse and composable-arrow product. `_hgroupoid : IsPresheafGroupoid s t e i c`
  supplies all test-scheme laws and uses composition of the first arrow after the second.
  Naturality comes from these being natural transformations.
- `_hs` and `_ht` require `LocallyOfFiniteType` on every representable etale scheme chart.
  `yoneda.preimage` recovers its unique scheme map to U; it adds no data or hypotheses.
- `_hj` tests `IsUnramified f.left` on every compatible pair of etale scheme charts of
  R and the relative product U times U. This is exactly the node's chartwise unramified
  relation map `prod.lift s t`, not unramifiedness of s or t.

Conclusions, clause by clause:

- The first conjunct is `IsRepresentableWith IsClosedImmersion` of the actual relative
  diagonal of `prod.lift s t`, expressing separatedness of j.
- The second conjunct tests `LocallyOfFiniteType f.left ∧ LocallyQuasiFinite f.left`
  in compatible charts, retaining the finite-type requirement that Mathlib's bare
  `LocallyQuasiFinite` omits. This is the locally quasi-finite clause with discrete
  finite-type field fibres. No quasi-compactness of the whole map is required.
- `∃ Z E sz tz` gives an S-scheme and an actual Yoneda isomorphism `E` representing R.
  The equalities `E.hom ≫ s = yoneda.map sz` and its t counterpart retain both field maps.
  `Z.left.IsSeparated` is absolute scheme separatedness.
- For every `z : Z.left`, the open `V` has carrier `{z}`, is closed, and has an isomorphism
  `a : V.toScheme ≅ Spec A`. `IsLocalRing A` includes nontriviality and a unique maximal
  ideal; `IsArtinianRing A` is the descending-chain condition. The two `RingHom.Finite`
  clauses use the actual maps `a.inv ≫ V.ι ≫ sz.left` and its t analogue. They mean finite
  module dimension over the field for each of the two structures. These singleton clopen
  affine components are disjoint and cover Z, which is equivalently the stated arbitrary
  disjoint union. No finiteness of the number of components is asserted.
- `P,p` give an open immersion into Z with closed range; `Subsingleton P.left` makes it a
  one-point component (nonemptiness follows from ep, or from its local coordinate ring).
  `B,a` identify it with `Spec B`. `IsLocalRing B`, `IsArtinianRing B`, `sigma.Finite` and
  `tau.Finite` give its ring properties for both structures.
- `sigma,tau` are tied to `sp,tp` by the displayed Spec equations. `epsilon` is tied to
  the restricted unit `ep` by its Spec equation; it is not an arbitrary augmentation.
  Surjectivity and `epsilon x = 0 ↔ ¬ IsUnit x` identify its kernel with the unique maximal
  ideal. Thus it identifies B's residue field with K. The equations
  `epsilon.comp sigma = RingHom.id K` and its tau counterpart state that both structural
  residue maps induce identity on K.
- `sp.left.IsFiniteLocallyFree` and its tp counterpart use the recorded finite, flat,
  locally-finite-presentation predicate.
- `IsPresheafGroupoid` for the restricted Yoneda maps supplies all restricted laws. The
  next four equations retain source, target, unit and inverse from the original groupoid.
  The universally quantified compatible `v,w` pairs express that the restricted composition
  cp agrees with c on all composable test arrows. Pullback universality supplies w, so this
  implication is nonvacuous. Since P represents this presheaf, cp is a scheme morphism by
  fully faithful Yoneda; no arbitrary replacement composition is being assumed.
- The `∀ H v w` cancellation clause expresses monicity of `(sp,tp)` on all test-scheme Hom
  sets. The final `∀ H, Equivalence ...` states reflexivity, symmetry and transitivity of
  the image of `P(H)` in `U(H) × U(H)` explicitly.

Dependency declarations read and reused:

- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`,
  `AlgebraicSpace.IsEtale`, `AlgebraicSpace.IsRepresentableWith`, and `IsAlgebraicSpace`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceGroupoid`: `IsPresheafGroupoid` (every field read),
  already landed under `def-sfb-algebraic-space-groupoid`; this is the appropriate general
  interface. `Sheaf.AlgebraicGeometry.GroupoidScheme.IsGroupoidScheme` is scheme-only,
  so it is retained as the recorded proof-dependency import, without copying its notion.
- Mathlib `Field`, `LocallyOfFiniteType`, `IsClosedImmersion`, `IsOpenImmersion`,
  `Limits.pullback`, its projections and universal maps, `IsSeparated`, `LocallyQuasiFinite`,
  `IsLocalRing`, `IsArtinianRing`, and `RingHom.Finite`.
- `Sheaf.AlgebraicGeometry.UnramifiedMorphism`: `AlgebraicGeometry.IsUnramified` is the
  exact locally-finite-type and open-diagonal conjunction, used in the chart hypothesis.
- `WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree`:
  `Scheme.Hom.IsFiniteLocallyFree` extends `IsFinite`, `Flat`, `LocallyOfFinitePresentation`.
- Stated proof dependencies are imported plainly: fibre-product/etale-cover calculus;
  unramified field-fibre decomposition; field-groupoid stabilizer dimension;
  unramified base-change/open restriction; unramified implies locally quasi-finite;
  and Mathlib Hopkins--Levitzki for Artinian local nilpotence. The unramified permanence
  and zero-dimensional field-space component nodes have no Lean record to import yet.

Edge cases checked: the trivial groupoid has P = Spec K; a constant etale group may have
infinitely many components, with identity component Spec K; a finite purely inseparable
pair groupoid allows nonreduced local Artinian B and different structural field maps;
a separable/Galois pair groupoid permits multiple components and requires monicity only
on P. R cannot be empty because the field unit maps into it. Empty test schemes remain
allowed. Neither K nor S is required perfect or Noetherian, and no independent smaller
universe of test schemes is introduced. The zero ring is excluded for each local component
by IsLocalRing, as intended.

Searches actually run before writing:

- `msearch.py ... leanfinder "field groupoid identity component finite relation algebraic
  space"`: eight hits, including finite identities, manifold structure groupoids, an affine
  spectrum criterion, and unrelated field facts; none states the target.
- `msearch.py ... loogle "AlgebraicSpace, IsGroupoidScheme, Spec K"`: zero hits, unknown
  identifier AlgebraicSpace in Mathlib's search service; this is not evidence that the
  project's AlgebraicSpace is absent.
- `msearch.py ... grep "AlgebraicSpace.*Groupoid|groupoid.*AlgebraicSpace" Sheaf`: zero hits.
- `msearch.py ... grep "fieldGroupoid.*identity|identity.*[Ff]inite[Rr]elation|IsPresheafGroupoid"
  AlgebraicGeometry`: zero Mathlib hits.
- Direct `rg` in both `lean/WeilConjectures` and `lean/Sheaf` for field groupoid, stabilizer,
  finite relation and identity component found the landed `AlgebraicSpaceGroupoid` and
  `FieldGroupoidStabilizerDimension` modules. Their complete signatures/docstrings were
  read and reused. The target id and proposed declaration name have no existing match.
  Scheme-only `GroupoidScheme` and the finite affine quotient theorem do not state this
  algebraic-space identity-component result.

Validation: `scompile.py` compiled the module as sandbox and as its intended library name,
with no errors or warnings. Every variable and universe is explicitly bound and
`autoImplicit` is disabled. The only postponed proof is this named target theorem, with
all six DAG proof steps in its docstring.

## Second reading by Q13

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
