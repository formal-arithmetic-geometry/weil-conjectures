## Worker report

The module `Sheaf.AlgebraicGeometry.SfEtaleCompactProjectionCoherence` defines
`AlgebraicGeometry.Etale.sfEtaleCompactProjectionInverse` and states four theorems
with `sorry`: naturality in each argument, tensor associativity, and composition
for the specified graph comparison. All five declarations belong to this node.
The definition uses the actual `projectionMapOfCompactification`, not a new
projection or an arbitrary isomorphism. There are no new nodes, dependency
repairs, statement corrections, or disputed assertions.

Clause-by-clause correspondence:

- Finite commutative coefficients: every declaration binds
  `(A : Type (u + 1)) [CommRing A] [Finite A]`. This follows the recorded etale
  module size convention, including the zero ring; no nontriviality is assumed.
- Arbitrary schemes: `X Y Z : Scheme.{u}`. There are no Noetherian, quasi-compact,
  separated-base, finite-type-morphism, or boundedness binders.
- A morphism supplied with open-then-proper factorization: `{f : X ⟶ Y}` and
  `(c : Compactification f)`. For composition, `(f : X ⟶ Y) (g : Y ⟶ Z)` and
  `cf`, `cg`, `ch : Compactification (f ≫ g)` supply the three factorizations.
  A Compactification's open immersion is not required to be quasi-compact.
- The ordinary unbounded categories are `DerivedCategoryModule A X`, and likewise
  for Y and Z. The functor F is exactly
  `rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c`.
- The canonical inverse projection q is `sfEtaleCompactProjectionInverse A c M P`.
  Its body is `@inv` applied to the existing projection component and its
  `IsIso` proof `(sfEtaleAmbientAdjointProjection A c).2 M P`. Its declared source
  is F(M tensor Lf*P), and its target is FM tensor P. Thus its data is a real
  canonical inverse, justified by the dependency's invertibility assertion.
- Naturality in M is
  `sfEtaleCompactProjectionInverse_naturality_left`: for every `a : M ⟶ N`,
  `F(a tensor 1) ≫ q(N,P) = q(M,P) ≫ (F(a) tensor 1)`.
- Naturality in P is
  `sfEtaleCompactProjectionInverse_naturality_right`: for every `b : P ⟶ Q`,
  `F(1 tensor Lf*(b)) ≫ q(M,Q) = q(M,P) ≫ (1 tensor b)`.
- Tensor means the existing bifunctor `derivedTensor (ModuleCat.{u + 1} A) X`.
  Tensor on morphisms uses its `.map` or `.obj M |>.map`; there is no different
  tensor instance or file-local notation.
- `sfEtaleCompactProjectionInverse_associativity` states the first identity.
  The left side is `q(M,P tensor Q)` followed by the inverse target associator.
  On the right, F first maps `1_M tensor (leftDerivedUpperStarTensorIso ...).hom`
  followed by the inverse source associator. It then applies
  `q(M tensor Lf*P,Q)` and `q(M,P) tensor 1_Q`. Both paths have the exact source
  F(M tensor Lf*(P tensor Q)) and target (FM tensor P) tensor Q of the node.
- `sfEtaleCompactProjectionInverse_composition` states the second identity.
  The left side is `q_h ≫ (E_M tensor 1_K)`. E is the existing, explicit
  `sfGraphCompactSupportCompIso A f g cf cg ch`, not a quantified comparison.
  The right side applies E at M tensor Lh*K, maps the canonical pullback
  compositor through F_f and F_g, applies F_g(q_f(M,Lg*K)), then q_g(F_fM,K).
  `leftDerivedUpperStarComp ... f g` supplies h* -> g* followed by f*.
  The node's right-to-left function composition is Lean's left-to-right `≫`.
- Both equalities concern actual morphisms in these derived categories, not their
  homology, geometric stalks, bounded subcategories, or mere existence predicates.

Dependency declarations read and used:

- `Sheaf.AlgebraicGeometry.SfEtaleAmbientAdjointProjection`:
  `AlgebraicGeometry.Etale.sfEtaleAmbientAdjointProjection`; the second conjunct
  supplies exactly invertibility of the canonical compactification projection.
- `WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Comparison`:
  `AlgebraicGeometry.Etale.leftDerivedUpperStarTensorIso`, obtained from
  `leftDerivedUpperStarTensorNatIso`, and its defining comparison. The recorded
  exactness identification `leftDerivedUpperStarIsoMapDerivedCategory` and the
  composition constraint `leftDerivedUpperStarComp` are in `Derived.UpperLowerStar`.
- `Sheaf.AlgebraicGeometry.SfGraphCompactSupportComposition`:
  `AlgebraicGeometry.Etale.sfGraphCompactSupportCompIso`. I read both this
  definition and `sfGraphCompactificationComparison` fully: the latter uses the
  two graphs and their common open intersection, and the former uses the product
  of the proper parts, its open over Y, and proper/open interchange, as required.
- Through those public interfaces, the already defined `derivedTensor`,
  `derivedTensorAssociator`, `projectionMapOfCompactification`, ordinary
  `DerivedCategoryModule`, and `rightDerivedLowerShriekOfCompactification` are used.

The stated proof dependencies are imported with plain `import`, including the
proper projection, open projection, ringed monoidal comparisons, site derived
 tensor descent, open projection composition, ringed projection tensor composition,
and the proper/open scheme-property modules. The proof-only nodes
`lem-sf-etale-proper-open-tensor-square` and
`lem-sf-etale-locally-closed-graph-model` currently have no Lean records, so there
is no module to import for them. They are not statement prerequisites: E is
already constructed in the recorded composition dependency. No proof dependency
has been restated or assumed as a hypothesis.

Edge cases were checked from the types and constructions. The zero ring is
finite and commutative and is not excluded. Empty schemes and zero complexes
are permitted. M, P, Q, K are completely arbitrary unbounded objects. Identity
morphisms and identity factorization parts are permitted; their canonical
pullback compositors and graph comparison are retained rather than replaced by
an assumed strict identity. Non-qc open parts remain permitted because the only
factorization binder is Compactification. No new universe equality is imposed:
`Scheme.{u}`, `ModuleCat.{u+1} A` and `A : Type (u+1)` are exactly the recorded
ordinary-etale module interfaces.

Searches made (2026-10-22):

- msearch.py / LeanFinder: "Derived compact support projection formula is
  compatible with tensor associativity and graph compactification composition".
  Eight hits about compactly supported continuous maps and test functions;
  none is this statement.
- msearch.py / Loogle: `"projectionMap"`. Zero hits.
- msearch.py / grep: `projectionMapAssociativity|ProjectionCompCompatible`.
  Zero Mathlib hits.
- msearch.py / LeanSearch: "Coherence of projection formula with tensor
  associativity and compact support composition". Eight hits about Cartesian
  monoidal categories and generic associator identities; no match.
- rg in both `lean/WeilConjectures` and `lean/Sheaf` for
  `projectionMapAssociativity`, `ProjectionCompCompatible`, projection coherence
  and the proposed new declaration name. The upstream
  `LowerShriekCompositionCoherence.projectionMapAssociativity` uses a chosen
  compactification; `exists_rightDerivedLowerShriekCompIso` asserts existence of
  some compatible E and additionally a base-change clause. Neither specifies
  the graph-normalized E for all three supplied compactifications. The new
  statement therefore reuses their canonical projection constructions without
  recording that stronger, differently quantified upstream theorem as a match.
  Existing completed/pro-etale/constructible coefficient-coherence modules are
  different categories and hypotheses and do not state the present node.
- rg for the node ID in upstream WeilConjectures: no match.

Validation: scompile.py compiled the sandbox and its actual library module
successfully (10.9 s and 9.8 s); no errors or warnings. Every theorem proof is
`sorry`; the single definition contains no `sorry`. The earlier compile's extra
implicit argument to `@inv` was removed. The file uses module mode, explicit
universes and binders, and has no line exceeding 100 characters.

## Second reading by Q158

A separate rereading pass by this same worker, with both the JSON statement and
final module open; the dispatcher explicitly prohibits starting other agents.
I checked the entire statement, not just the primary recorded declaration.

The finite coefficient binder and arbitrary scheme binders are present in every
declaration. The supplied c, cf, cg, ch exactly encode the stated open/proper
factorizations, and the zero ring, identity maps and non-qc opens are not dropped.
The helper inverts the dependency's precise projection component, so there is no
choice of a substitute projection. Both naturality squares have the correct
source and target. In the associativity equation, the source pullback comparison
has direction f*(P tensor Q) -> f*P tensor f*Q, and the two associators are inverse
associators, giving the node's requested parenthesizations. In composition,
`sfGraphCompactSupportCompIso` has direction F_h -> F_f then F_g; its component
on M is tensored on the left side, its component on M tensor h*K starts the right
side. The next map is exactly F_g F_f of `1_M tensor (h* -> f*g*)`, which is the
implicit constraint in the node. The remaining arrows are F_g(q_f) then q_g.
All maps are typed as derived morphisms with no stalkwise surrogate.

No semantic mismatch was found. No changes to the node statement, dependencies,
proof plan, or dependency records were needed. Only `lean` is changed in the
copied node. All four theorem signatures are represented in lean.declarations,
with the composition signature recorded verbatim as lean.statement.
