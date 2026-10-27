## Worker report

The module `Sheaf.AlgebraicGeometry.EquivariantStableModelEvaluation` states the node in three
named theorems, all with `sorry` proofs. There are no new definitions, axioms, instances or
private constructions. The main declaration is
`AlgebraicGeometry.exists_equivariant_stable_model_evaluation`; its two companions are
`AlgebraicGeometry.stable_model_dominant_baseChange_integral` and
`AlgebraicGeometry.stable_model_finite_baseChange_functionField`.

The source is de Jong, *Families of curves and alterations* (1997), §§3.9--3.13, printed p.609,
read at https://aif.centre-mersenne.org/item/10.5802/aif.1575.pdf. Section 3.9 constructs the
birational Hom closure; 3.10--3.12 prove properness and equivariant evaluation. Section 3.8
explains normal equivariant domination and unordered markings. The node's retained proof
Steps 6--10 give the more general flat generic-field calculation. No change to the accepted
natural-language statement or proof is needed.

### Hypotheses of the model-existence theorem

| Node hypothesis | Lean |
| --- | --- |
| A field k | `(k : Type u) [Field k]` |
| S a k-scheme, with its specified structure | `S : Scheme.{u}`, `pS : S ⟶ Spec (.of k)` |
| Integral | `[IsIntegral S]` |
| Normal, with integrally closed domain local rings | `hnormal : ∀ x, IsDomain (S.presheaf.stalk x) ∧ IsIntegrallyClosed ...` |
| Projective in the H-projective convention | `[IsHProjective pS]` |
| Finite type over k | `[LocallyOfFiniteType pS]`; quasi-compactness follows from H-projectivity/properness, so no extra quasi-compact hypothesis |
| Function field L | `S.functionField`, the existing generic stalk, with `S.fromSpecFunctionField : Spec L ⟶ S` |
| W over S and Q over S | `f : W ⟶ S`, `g : Q ⟶ S` |
| Both H-projective | `[IsHProjective f]`, `[IsHProjective g]` |
| The finite list of sections, including n=0 | `n : ℕ`, `s : Fin n → (S ⟶ W)`, `hs : ∀ i, s i ≫ f = 𝟙 S` |
| Stable pointed family | `hstable : IsStablePointedCurve f s hs`, the recorded definition, including flatness, finite presentation, connected reduced nodal curve fibres, disjoint smooth markings and component stability |
| Smooth geometrically integral generic fibre | `Smooth` and `GeometricallyIntegral` on `pullback.snd f S.fromSpecFunctionField` |
| No nonconstant geometric projective-line maps into Q | `hnoRational`, quantifying over every algebraically closed Ω and `t : Spec Ω ⟶ S`; an Ω-map `a` factors through an Ω-point `q` |
| Finite group J | `(J : Type v) [Group J] [Finite J]` |
| Compatible actions on k,S,W,Q | `σk : J →* Aut (Spec k)`, `σS`, `σW`, `σQ`, and commuting-square identities `hk`, `hf`, `hg` |
| Semilinear actions allowed | `σk` is arbitrary; no requirement that it be the identity. Spectrum automorphisms are the contravariant encoding of field automorphisms. |
| Nonfaithful actions allowed | No injectivity hypothesis on any action homomorphism |
| Union of markings preserved | `hmark : ∀ a, ∃ π : Equiv.Perm (Fin n), ∀ i, s i ≫ (σW a).hom = (σS a).hom ≫ s (π i)` |
| Equivariant generic S-morphism | `uη`, `huη` for its base-map identity, and `hequiv` using explicit `pullback.map` terms on source and target, with `Spec.map (Scheme.functionFieldAut (σS a)).hom` on the generic base |

For the marking encoding, S is integral and hence connected and nonempty. Its labelled disjoint
sections are the disjoint components of their finite union. Preservation of that union therefore
gives exactly a permutation of the labels for each group element. No chosen action on the label
set, nor faithful action on the schemes, is assumed.

### Conclusions of the model-existence theorem

| Node clause | Lean |
| --- | --- |
| An integral scheme R and projective birational map R→S | Existential `R`, its `IsIntegral` proof, `r`, `IsHProjective r`, and a dense open `U` with `IsIso (r ∣_ U)` |
| J acts on R and R→S is equivariant | `σR : J →* Aut R`, `hr` |
| Evaluation W_R→Q_R | `e : pullback f r ⟶ pullback g r` with its second-projection identity |
| Evaluation equivariant | The `∀ a : J` pullback-map identity after `pullback.fst g r`; together with the second-projection identity, this is equivariance into Q_R |
| Extends the specified generic morphism | `aη : Spec L ⟶ R`, `haη`, and the equality using the explicit `pullback.map f S.fromSpecFunctionField f r (𝟙 W) aη (𝟙 S) ... ≫ e ≫ pullback.fst ...` with `uη ≫ pullback.fst ...` |
| Normal integral finite-type projective k-scheme S' | Existential `S'`, `IsIntegral S'`, the stalkwise normal condition, `IsHProjective (r' ≫ pS)` and `LocallyOfFiniteType (r' ≫ pS)`; H-projectivity supplies quasi-compactness |
| Finite group J' and a surjection ρ | Existential `J' : Type v`, its `Group` and `Finite` instances, `ρ : J' →* J`, and `Function.Surjective ρ` |
| Compatible action on S' | `σS'` and `hr'`; compatibility with the ground-field action through ρ follows by composing `hr'` and `hk` |
| H-projective alteration S'→S | `IsHProjective r' ∧ IsProper r' ∧ Surjective r'`, finite over a dense open, and the canonical finite extension of function fields |
| Equivariant S-map S'→R | `b`, `hb : b ≫ r = r'`, and the displayed identity with `σR (ρ a)` and `σS' a` |
| L'=k(S')/L finite separable | Algebra instance constrained by `algebraMap ... = (r'.functionFieldMap hη).hom`, then `Module.Finite` and `Algebra.IsSeparable` |
| Fixed field of ker ρ is L | For every `x : S'.functionField`, fixed by every `a` with `ρ a = 1` iff `x = algebraMap ... y` for some `y : S.functionField`; actions are the actual `Scheme.functionFieldAut` stalk actions |
| Pulled-back evaluation | `e'` over S' with its first projection equal to the explicit `pullback.map f r' f r (𝟙 W) b (𝟙 S) ... ≫ e ≫ pullback.fst ...`; both projection equations uniquely characterize the actual pulled-back map |
| Pulled-back stable pointed curve and projectivity | `IsStablePointedCurve (pullback.snd f r')` on `f.baseChangeSection` with the existing `baseChangeSection_snd` proofs, and `IsHProjective (pullback.snd f r')` |
| J'-equivariant evaluation and markings | The last two `∀ a : J'` clauses, through `σW (ρ a)`, `σQ (ρ a)` and `σS' a` |

The final evaluation extends `uη` by its pullback characterization and the preceding extension
identity for `e`. The chosen generic lift `aη` is the lift over the dense-open birational
isomorphism; its base identity suffices to determine that lift. The output does not require
J'=J or L'=L, though those choices are available in the node's proof.

### Arbitrary integral base change and generic fields

`stable_model_dominant_baseChange_integral` states the general flat-family part of Steps 6--7.
It assumes only the properties used in that part of the node's proof: integral S, flat f, and
smooth geometrically integral generic fibre. For every integral T and dominant `t : T ⟶ S`
it asserts `IsIntegral (pullback f t)` and smoothness and geometric integrality of its generic
fibre, represented by the iterated second projection over `T.fromSpecFunctionField`.
Thus it applies to the given stable family, since its predicate includes flatness. In particular
T=S and t=id give integrality of W, via the canonical identity-base-change isomorphism.
No finiteness, normality, projectivity or Noetherian hypothesis on T is introduced.

`stable_model_finite_baseChange_functionField` states Steps 8--10. Its `[IsIntegral W]` makes
D=k(W) available; this is the just-established conclusion, not a new condition on the original
input. The theorem itself supplies integrality of W_T as an existential instance and records
the generic-point identities for f,t and the two projections. It then quantifies over algebra
structures on D and L_T constrained to equal those actual generic stalk maps. Such structures
always exist, by `RingHom.toAlgebra`; they are not arbitrary additional morphisms or choices.

For finite `Module.Finite S.functionField T.functionField`, the conclusions are explicitly
`IsField (W.functionField ⊗[S.functionField] T.functionField)` and a ring equivalence with
`(pullback f t).functionField`. Its pure-tensor equation sends d⊗a to the product of the two
canonical generic pullbacks. This identifies the natural map, not merely abstract isomorphic
fields. The multiplicative structure is Mathlib's `Algebra.TensorProduct` multiplication
(d⊗a)(d'⊗a')=dd'⊗aa', on the existing module tensor product.

For any compatible finite group actions `σW`, `σT`, `σS`, the last clause supplies a diagonal
action `σX : G →* Aut (pullback f t)`, commuting with both projections. Its generic-field action
under the same equivalence satisfies g(d⊗a)=g(d)⊗g(a) on pure tensors. The factors may act
nontrivially on L, so this is semilinear equivariance. Pure tensors generate the tensor algebra,
so the equation is equivariance on the whole algebra. This avoids assuming or choosing a
linear tensor action when the scalar action is nontrivial.

Iteration is contained in these universal statements: replace S by any preceding integral
base T and f by its base-changed family. Flatness survives base change and the preceding
theorem gives its smooth geometrically integral generic fibre. The same theorems then apply
to every further dominant integral base. The field theorem assumes finiteness alone, not
separability, so includes every finite purely inseparable extension in positive characteristic
and the equality case in characteristic zero.

### Dependency declarations used

All recorded statement-dependency nodes were read, together with their Lean records or Mathlib
matches, and the definitions/signatures/docstrings in source.

| Node(s) | Module and declaration |
| --- | --- |
| def-kun-projective | `WeilConjectures.AlgebraicGeometry.Morphisms.Projective`, `AlgebraicGeometry.IsHProjective` |
| def-kun-topological-krull-dimension | `Mathlib.Topology.KrullDimension`, `topologicalKrullDim` (inside stable fibres) |
| def-pc-fibre-product, def-weil-geometric-fibre | `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`, `pullback`, `pullback.fst`, `pullback.snd`, `pullback.map` |
| def-pc-field-extension | `Mathlib.Algebra.Algebra.Defs`, `Algebra`, `algebraMap`, `RingHom.toAlgebra` |
| def-pc-field-tower | `Sheaf.FieldTheory.FieldTower`, the convention of `Module.Finite` and `Algebra.IsSeparable` for finite separable extensions (the supplementary degree definition is not needed) |
| def-pc-geometrically-irreducible | `Mathlib.AlgebraicGeometry.Geometrically.Integral`, `GeometricallyIntegral` |
| def-pc-integral-scheme | `Mathlib.AlgebraicGeometry.Properties`, `IsIntegral` |
| def-sbc-locally-finite-presentation | `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`, `LocallyOfFinitePresentation`, used within `IsStablePointedCurve` |
| def-sbc-smooth-morphisms | `Mathlib.AlgebraicGeometry.Morphisms.Smooth`, `Smooth` |
| def-sc-function-field | `WeilConjectures.AlgebraicGeometry.FunctionField` explicitly directs integral users to Mathlib `Scheme.functionField`, which is used here |
| def-sfb-quasi-split-nodal-fibres | `Sheaf.AlgebraicGeometry.QuasiSplitNodalFibres`, `HasQuasiSplitNodalFibres`, read/imported; quasi-splitness is defined in the node's conventions but not assumed or asserted by this lemma |
| def-sfb-stable-pointed-curve | `Sheaf.AlgebraicGeometry.StablePointedCurve`, `IsStablePointedCurve` |
| def-weil-closed-immersion | `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`, `IsClosedImmersion`, through `IsHProjective` |
| def-weil-field | `Mathlib.Algebra.Field.Defs`, `Field` |
| def-weil-finite-integral-morphism | `Mathlib.AlgebraicGeometry.Morphisms.Finite`, `IsFinite` |
| def-weil-finite-type-morphism | `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`, `LocallyOfFiniteType`, with `QuasiCompact` supplied by H-projectivity |
| def-weil-flat-morphism | `Mathlib.AlgebraicGeometry.Morphisms.Flat`, `Flat` |
| def-weil-pbc-module-tensor-product | `Mathlib.LinearAlgebra.TensorProduct.Defs`, `TensorProduct`, with algebra multiplication from `Mathlib.RingTheory.TensorProduct.Basic` |
| def-weil-proper-morphism | `Mathlib.AlgebraicGeometry.Morphisms.Proper`, `IsProper` |
| def-weil-surjective-morphism | `Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap`, `Surjective` |
| Proof dependency lem-sfb-high-genus-hom-closure | `Sheaf.AlgebraicGeometry.HighGenusHomClosure`, imported without `public` for the three existence/naturality/action theorems; its helper abbreviations are expanded in the signature |

The Hom-closure theorem remains in `proof_deps` only. Its two helper definitions are expanded
to the exact Mathlib `pullback.map` terms in the main signature. The item's `stmt_deps` is
identical to the live base, and the only changed node field is `lean`.
Additional canonical interfaces read and reused: `Scheme.Hom.functionFieldMap` from
`WeilConjectures.AlgebraicGeometry.Curve.DivisorPullback` (generic stalk map),
`Scheme.functionFieldAut` from `WeilConjectures.AlgebraicGeometry.StalkAut`, and
`Scheme.Hom.baseChangeSection`/`baseChangeSection_snd` from
`WeilConjectures.AlgebraicGeometry.DeformationSpace.BaseChangeSection`.

Recorded proof-dependency modules are imported, including projective base change, properness,
H-projective composition, finite projective bundles, the ample/projective-bundle comparison,
normalization, stable generic extension, flat torsion-freeness, affine fibre products and the
finite-dimensional-domain field criterion. The proof-only
`lem-sfb-finite-normalization-model-functoriality` currently has neither Lean record nor
Mathlib match, so has no module to import. Its absence does not prevent this statement: all
objects used in the signature already exist. The current file states no normalization theorem
and makes no new definition depending on that unstated result.

### Edge cases checked

- n=0: `Fin 0` and its unique permutation are allowed; no positive marking hypothesis.
- Trivial groups and nonfaithful actions: no faithful or injective action condition.
- Semilinear ground-field action: `σk` need not be trivial; all base compatibility is retained.
- dim S=0 and constant generic evaluation: neither is excluded.
- Q nonintegral, nonreduced or nonflat: no additional property of Q is assumed.
- Empty Q: the generic morphism is impossible since W's generic fibre is nonempty; no hidden
  nonemptiness assumption on Q is added.
- General T: integral means nonempty; T may be non-Noetherian and not finite type.
- Degree-one field extensions and identity base changes: finite field theorem and canonical
  tensor normalization include them.
- Finite purely inseparable extensions: no separability condition in either base-change theorem.
- Successive dominant integral base changes: the generic-fibre clauses and base-changed flatness
  let the same statements apply again.
- Universes: schemes and test fields use one arbitrary u, as in Mathlib's scheme/base-change API
  and the dependency statements; finite groups use independent v. No universe equality is imposed.

### Searches and validation

All searches used the prescribed `msearch.py NN lem-sfb-equivariant-stable-model-evaluation`
wrapper, or read-only rg in the named source directories.

- LeanFinder: “An equivariant generic morphism from a stable pointed curve to a projective
  scheme without rational curves extends after projective birational base change”. Eight
  unrelated/preimmersion, Weierstrass and rational-map hits; no exact existing statement.
- Loogle: `AlgebraicGeometry.IsStablePointedCurve, AlgebraicGeometry.GeometricallyIntegral`.
  No hits; Mathlib's endpoint does not know the project's stable-curve predicate.
- LeanSearch: “function field integral flat family geometrically integral generic fibre finite
  base change tensor product”. Eight results, including `Scheme.functionField`, its field
  instance, integral-morphism base change and integral tensor algebras; no exact theorem.
- Mathlib grep via msearch: `stable.*model.*evaluation|functionField.*tensor|tensor.*functionField`
  in `AlgebraicGeometry`: zero hits.
- Project/upstream rg for the item id in `lean/WeilConjectures` and `lean/Sheaf`: no existing
  declaration. Searches by `HighGenus`, `StablePointed`, `equivariant`, `functionFieldMap`,
  `functionFieldAut` located the reused canonical interfaces described above.
- Final declaration-name search across Mathlib, `lean/WeilConjectures` and `lean/Sheaf`: no
  collisions with any of the three new names.
- Server `scompile.py`: initial compile isolated a generic-point pullback category annotation
  in the tensor clause. Supplying `(C := Scheme.{u})` fixed it. Subsequent server compiles
  passed without errors or warnings. Every theorem proof remains `sorry`.

No new nodes. No dependency modules. No statement correction or STATEMENT-DISPUTED issue.
The example `CompactObject.lean` has been withdrawn in the current read clone and contains
no declarations; its node points to Mathlib `CategoryTheory.IsCompactObject`. The delivered
header and module visibility follow the active stable-curve/Hom-closure example modules.

## Second reading by NN

This is this worker's separate clause audit, not a claim that another agent reviewed the packet;
the task explicitly prohibits starting agents and assigns independent review to the maintainer.
I reopened the original node and compared it with all three signatures after compilation.

The main theorem includes k, normal integral projective finite-type S, the specified stable
marked family, H-projective Q, every geometric rational-map exclusion, all four compatible
semilinear actions, permutation of markings and equivariant generic evaluation. Its nested
existentials provide R, its action, the extending evaluation, S', J', surjection, alteration,
factorization, canonical finite separable field extension and fixed-field identity. Both
pulled-back curve and evaluation, including marking permutations, are present.

The two remaining signatures cover the arbitrary integral T clause and finite field clause.
Integrality of W used to name D follows by the identity base case of the first companion.
The finite theorem imposes no separability and fixes the ring equivalence on pure tensors.
I made the tensor algebra's field property explicit as `IsField`, and replaced a version
merely quantifying over compatible pullback automorphisms by an existential diagonal group
action with both projection identities. This makes existence and compatibility explicit.
The generic-point category annotation is solely elaboration, not a size or mathematical
restriction. No changes to the node's natural-language statement were necessary.


## Returned delivery repair: H2

The return on immutable head `0837cbf6fe25` identified one defect: adding the theorem
`lem-sfb-high-genus-hom-closure` to statement dependencies to own its plain helper definitions.
I selected the reviewer's second correction: inline the explicit Mathlib `pullback.map`
terms and remove the theorem statement dependency. No new definition node is introduced.

- The two `genericHomSourceAction` occurrences in `hequiv` are expanded to `pullback.map`
  with source/target automorphisms, the canonical `Spec.map (Scheme.functionFieldAut ...).hom`
  and the base-compatibility identity from the existing `WeilConjectures.AlgebraicGeometry.StalkAut` API.
- The two `homParameterMap` occurrences (generic extension and pulling evaluation to S')
  are expanded to `pullback.map` with identity on W and S, and the specified parameter
  map `aη` or `b`. Category identity laws and `haη.symm`/`hb.symm` supply exactly the
  commutative-square proof arguments of the original definition.
- `Sheaf.AlgebraicGeometry.HighGenusHomClosure` is now a non-public proof import;
  `WeilConjectures.AlgebraicGeometry.StalkAut` is explicitly public for the canonical
  function-field automorphism used directly in the signatures.
- `stmt_deps` is restored to the current live base's list. `proof_deps` still contains the
  Hom-closure theorem. All natural-language node fields, all three theorem conclusions,
  and all dependency node records are retained. The companion theorem signatures are
  unchanged from the returned head.
- Refreshed `lean.statement` verbatim from the expanded main signature, including every
  map and compatibility proof. The JSON keeps indent 1, Unicode and its final newline.

I compared the retained sandbox with the return's identified helper occurrences and with
current main: the original sandbox delta was `lean` plus the extra theorem `stmt_deps`;
the repaired delta is `lean` alone. The existing helpers' source definitions were reopened
at `HighGenusHomClosure.lean:48` and `:235`; each new map has their exact argument order,
so unfolding the old helpers yields the same signature, up to proof irrelevance of the
identity-law arguments. This addresses H2 without changing the mathematical statement.
The rest of the independent review's accepted clause audit continues to apply.

Repair validation: `scompile.py NN lem-sfb-equivariant-stable-model-evaluation` compiled the
expanded module in both sandbox and library modes without errors or warnings. All three
proofs remain `sorry`; no helper definition or theorem was added.
