## Worker report

The module `Sheaf.AlgebraicGeometry.GroupScheme.GaloisStableAffineLineGeneratedSubgroup`
states `AlgebraicGeometry.galoisStableAffineLine_generated_subgroup`. Its sole theorem
has proof `sorry`. Its only other declaration is the fully written Prop-valued helper
`AlgebraicGeometry.IsAffineLineGeneratedAfterBaseChange`, expanding the two clauses of
minimality in this very statement. It introduces no independent mathematical object,
no additional assumption, and no postponed data or subsidiary theorem.

The inherited BLOCKED ending was a stage-1 live-wins refusal. The current node has a
passing stage-1 review, no Lean record, and a stage-2 queue entry. The stage handoff in
`coord/brief-stage2.md` section 0 explicitly permits its stage-2 statement. The accepted
statement, dependencies, proof, and every other node field are preserved; only `lean`
is added. There is no released repair note for this item.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- The ground field is `(k : Type u) [Field k]`. Characteristic p>0 with p prime is
  `(p : ℕ) [Fact p.Prime] [CharP k p]`; primality entails positivity.
- The ambient k-group scheme is `(G : Over (Spec (.of k))) [GrpObj G]`.
  `[IsAffine G.left]`, `[LocallyOfFiniteType G.hom]`, and `[QuasiCompact G.hom]`
  give exactly affineness and finite type. `[Smooth G.hom]` gives smoothness.
  There is no connectedness, commutativity, torsion, unipotence, or perfectness
  hypothesis on G or k.
- The fixed separable closure is `(K : Type u) [Field K] [Algebra k K]
  [IsSepClosure k K]`. Mathlib's class means separably closed and algebraic
  separable over k, exactly the parenthetical meaning in the node. It does not
  require a finite extension or an algebraically closed K.
- Write b for `Spec.map (CommRingCat.ofHom (algebraMap k K))` in this report only.
  `Over.pullback b` is canonical scalar extension. The source of the family is
  `(Over.pullback b).obj (StandardGroupSchemes.additive k)`, namely the affine line
  over K: the existing additive group has coordinate algebra k[X]. Using its base
  change instead of a second model Spec K[X] preserves the canonical k-descent
  datum. Its zero section is `(Over.pullback b).map η[StandardGroupSchemes.additive k]`.
- The arbitrary set is `F : Set (A¹_K ⟶ G_K)` with exactly these two canonical
  objects. Its elements are morphisms in `Over (Spec K)`, so arbitrary K-scheme
  maps, with no group-homomorphism or finiteness assumption on the family.
- `hpointed` says for every member that the zero section followed by f equals
  `(Over.pullback b).map η[G]`. Both sides have domain the base-changed Spec k,
  canonically Spec K, so this is precisely f(0)=1 without changing the source
  zero or choosing an arbitrary point.
- `hstable` quantifies over every `σ : K ≃ₐ[k] K` and every f in F, and asks for
  f' in F satisfying `f'.left ≫ baseChangeMap G.hom (specAlgEquivOver σ) =
  baseChangeMap (StandardGroupSchemes.additive k).hom (specAlgEquivOver σ) ≫ f.left`.
  On coordinates this says f'^* = σ_A ∘ f^* ∘ σ_G⁻¹, hence f' is the coefficient
  conjugate of f. The semilinear maps are canonical isomorphisms. Applying the
  same condition to σ⁻¹ gives equality of the conjugated family with F, so this
  forward-membership form expresses stability exactly, not a stronger invariant
  parametrization and not pointwise fixation of every member.
- The conclusion binds an actual k-scheme L, its `GrpObj L`, and its embedding
  `i : L ⟶ G`. `@IsClosedSubgroupScheme ... i` is the recorded subgroup notion,
  including the closed immersion and compatibility of the group law.
- `IsAffine L.left ∧ LocallyOfFiniteType L.hom ∧ QuasiCompact L.hom` states the
  standing affine finite-type convention for the resulting group.
  `Smooth L.hom ∧ ConnectedSpace L.left` is exactly smooth and connected.
- The first conjunct of `IsAffineLineGeneratedAfterBaseChange k K G F L i`
  requires each f to factor through the actual base-changed inclusion i_K.
- Its second conjunct quantifies over every K-group H with a closed subgroup
  embedding j into G_K. If all f factor through j, there is an actual scheme
  morphism h : L_K → H satisfying h ≫ j = i_K. This is scheme-theoretic inclusion,
  retaining nilpotent structure. No smoothness, reducedness or connectedness is
  imposed on these competing subgroups. Affineness and finite type need not be
  separately assumed here: they follow from being a closed subscheme of G_K.
  The group law on G_K is the existing canonical `Functor.grpObjObj`, passed
  explicitly to `IsClosedSubgroupScheme`; it is not an arbitrary structure.
- The next conjunct quantifies over every other smooth connected affine finite-type
  closed k-subgroup i' satisfying the same generation predicate. Its conclusion
  `∃ e : L' ≅ L, e.hom ≫ i = i'` is equality as embedded subgroup schemes.
  It is the standard slice representation of equality of closed subgroups used
  by the already recorded Galois-descent node. It is stronger than an abstract
  isomorphism and expresses precisely the node's uniqueness.
- The last conjunct `F = ∅ → ∃ e : L ≅ 𝟙_ (Over (Spec (.of k))),
  e.hom ≫ η[G] = i` says that the empty family gives the identity subgroup
  with its specified inclusion into G.
- The preliminary sentence defining the phrase "vector group" introduces no
  datum, hypothesis, or conclusion in this lemma; the lemma does not assert
  that L is a vector group. No unnecessary vector-group assumption is added.

Dependency declarations read and used:

- `def-weil-field`: `Field`, Mathlib.Algebra.Field.Defs.
- `def-sc-group-scheme`: `CategoryTheory.GrpObj`,
  Mathlib.CategoryTheory.Monoidal.Grp, on `Over (Spec k)` as the node's record says.
- `def-weil-finite-type-morphism`: `AlgebraicGeometry.LocallyOfFiniteType` in
  Mathlib.AlgebraicGeometry.Morphisms.FiniteType and `AlgebraicGeometry.QuasiCompact`
  in Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact; finite type is their conjunction.
- `def-sc-group-scheme-subgroup`: `AlgebraicGeometry.IsClosedSubgroupScheme`,
  WeilConjectures.AlgebraicGeometry.GroupScheme.Defs (publicly imported through
  StandardGroupSchemes); its full signature requires the two group structures
  and its fields give a subgroup embedding and closed immersion.
- `def-sbc-smooth-morphisms`: `AlgebraicGeometry.Smooth`,
  Mathlib.AlgebraicGeometry.Morphisms.Smooth.
- `def-weil-connected-scheme`: `ConnectedSpace`,
  Mathlib.Topology.Connected.Basic, applied to the underlying scheme space.
- `def-sc-gm-ga`: `AlgebraicGeometry.StandardGroupSchemes.additive`,
  `additiveGroup`, `additiveGroup_existsUnique`, `additiveCounit`, `identitySection`
  in Sheaf.AlgebraicGeometry.StandardGroupSchemes. The actual coordinate algebra,
  zero counit, and uniquely specified group structure are reused, not reconstructed.
- `def-weil-affine-spectrum`: `AlgebraicGeometry.Spec` and `Spec.map`,
  Mathlib.AlgebraicGeometry.Scheme.
- `def-weil-polynomial-ring`: `Polynomial`, Mathlib.Algebra.Polynomial.Basic,
  through the existing additive affine-line construction.
- The existing canonical Galois map `AlgebraicGeometry.specAlgEquivOver` and
  `baseChangeMap` are exposed by WeilConjectures.AlgebraicGeometry.Picard.Jacobian,
  exactly as in Sheaf.AlgebraicGeometry.GaloisDescentAffineSubgroups. Their actual
  semilinear maps are used in hstable. `IsSepClosure` is the existing Mathlib
  class in Mathlib.FieldTheory.IsSepClosed.

All recorded statement modules are public imports, directly or through an owning
module. The proof plan imports the existing pointed-map generation, Galois descent,
algebraic-closure reducedness test, idempotent criterion, common-extension-field,
polynomial, quotient, geometric, smooth-group, and faithfully-flat modules. Basic
spectrum/closed-immersion/group/finite-type imports are already public dependencies.
The proof node `lem-sfb-vector-space-tensor-family-zero-detection` has no recorded
Lean module or Mathlib match, so there is no module to import for it yet. It is a
proof-only prerequisite and introduces no missing object in this statement.
The docstring contains all seven accepted proof steps, with dependency identifiers.

Edge cases checked before finalizing:

- F empty: both factorization quantifiers are valid, and the explicit identity
  isomorphism clause forces the identity closed subgroup.
- Constant identity maps: their generated subgroup is still the identity.
- Infinite F and infinite separable closure: no finite set, finite dimensional
  family, finite Galois group, or finite extension hypothesis is present.
- Imperfect k and nonperfect separably closed K remain permitted.
- For f(t)=t^p into G_a the scheme-theoretic generated subgroup is G_a; testing
  factorization through arbitrary closed subgroups does not replace it by α_p
  or its K-points. Nonreduced competing subgroups are explicitly allowed.
- For noncommuting root-line images in GL₂ no commutativity or p-torsion condition
  appears; the statement covers their generated SL₂ subgroup.
- A disconnected smooth ambient G is allowed; only the generated L is connected.
- The trivial ambient group and finite fields remain allowed. No Nonempty F,
  positive dimension, or nonconstant-member assumption is imposed.
- All scheme, field and algebra objects use one explicit universe u, as in the
  recorded group-scheme/subgroup interface. The family is the full set of maps
  between these objects; there is no smaller independent test-algebra universe.

Searches made (2026-10-24):

- msearch.py leanfinder: "The smallest closed subgroup containing a Galois stable
  family of pointed affine lines is smooth connected and descends to the ground
  field". Eight hits concerned Galois categories, fixed fields, or formally smooth
  algebras; none states subgroup generation by affine-line scheme morphisms.
- msearch.py loogle: `"IsClosedSubgroupScheme", "Smooth"`. No hits.
- msearch.py grep, AlgebraicGeometry: `generated.*subgroup|Galois.*stable.*affine`.
  No hits.
- rg of both WeilConjectures and Sheaf for the item id and prospective declaration
  names: no declaration of this item. Broader subgroup-generation/Galois searches
  found the pointed-map and Galois-descent dependencies, which are imported;
  neither has this family-generation statement.
- tools/blueprint_refs.py search `galois-stable-affine-line-generated`: zero blueprint
  matches. Direct DAG lookup found the assigned node and its recorded dependencies.
- Read the current node and every stmt_dep record, including Mathlib matches, then
  their declaration signatures and docstrings. Read the StandardGroupSchemes
  construction and GaloisDescentAffineSubgroups in full as relevant to the interface.

Source checked: Conrad's online PDF
https://math.stanford.edu/~conrad/papers/appbnew.pdf, printed p.12, Theorem 2.6,
opening proof sentence; the family/general-group form is exactly the accepted
stage-1 node, whose proof explicitly supplies the general generation argument.
No statement correction, dependency repair, new independent notion, or
STATEMENT-DISPUTED flag is needed.

Validation: scompile.py compiled the delivered file both as a sandbox module and
under its final library module name, each clean, in 2.8 and 2.9 seconds respectively.
The initial probe exposed the scoped canonical pullback-group instance; the final
statement passes `Functor.grpObjObj` explicitly instead of imposing any new
hypothesis, and states pointedness by equality with the base-changed identity.

## Second reading by Q100

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
