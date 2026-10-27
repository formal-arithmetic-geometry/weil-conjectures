## Worker report

The module `Sheaf.AlgebraicGeometry.TransverseSubgroupProductOpen` states
`AlgebraicGeometry.isOpenImmersion_transverse_subgroup_product`, with proof `sorry`.
It introduces no definitions and changes only the item's `lean` record. The statement,
accepted stage-1 split, dependency lists, and proof are retained verbatim in the node.

Source read: Milne, Algebraic Groups (2017), Theorem 13.33(d), printed pp.265–266,
and the smooth tangent/etale criterion on p.267. The source explicitly uses trivial
intersection as functors and the isomorphism on identity tangent spaces. The current
blueprint's `det-thm-sf-ctf-stability-direct-images` proof was also read to check the
inherited supporting route. This is a supporting algebraic-group lemma, not a unit statement.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- Algebraically closed field k: `(k : Type u) [Field k] [IsAlgClosed k]`.
- Group schemes over k: `(G H K : Over (Spec (.of k)))` and `[GrpObj G]`,
  `[GrpObj H]`, `[GrpObj K]`. The group laws need not be commutative.
- G affine: `[IsAffine G.left]`.
- G smooth: `[Smooth G.hom]`.
- G finite type: `[LocallyOfFiniteType G.hom] [QuasiCompact G.hom]`, exactly the
  conjunction specified by def-weil-finite-type-morphism. No extra finite-type
  hypothesis on H or K is imposed: it follows from their closed immersions into G.
- Smooth closed subgroups H and K: `(i : H ⟶ G) (j : K ⟶ G)` with
  `[IsClosedSubgroupScheme i] [IsClosedSubgroupScheme j] [Smooth H.hom] [Smooth K.hom]`.
  The recorded closed-subgroup class includes both the group homomorphism property and
  injectivity on all algebra-valued points, as well as the closed immersion.
- Identity tangent space: `schemeTangentSpace k G.left G.hom (GrpObj.onePoint G)`.
  Its addition is the canonical `schemeTangentSpaceAddCommGroup` instance from the
  recorded tangent-space module; it is not an arbitrary additive structure.
- Identify Lie(H) and Lie(K) with their images in Lie(G): for an ambient tangent
  vector `w.1`, membership in the H image is
  `∃ a : Spec (.of (DualNumber (G.left.residueField (GrpObj.onePoint G)))) ⟶ H.left,
  a ≫ i.left = w.1.val`; the K image uses `b ≫ j.left = w.2.val`.
  This uses the original tangent-vector definition, not a second tangent space.
  An inclusion is a monomorphism, so such a lift is unique and is necessarily over k
  (compose its factorization with G's structure map). Its closed-point restriction is
  the subgroup identity: both it and the identity section composed with the structural
  residue-field map have the same composite into G, so monicity makes them equal.
  Since the identity sections are k-rational, identifying their residue fields with k
  identifies these factorizations exactly with the usual inclusion tangent maps.
  Thus the two predicates specify precisely the two tangent subspaces in the node.
- Addition is a vector-space isomorphism from the direct sum: `hLie` says
  `∀ v, ∃! w : TG × TG, (H-image w.1) ∧ (K-image w.2) ∧ w.1 + w.2 = v`, with TG
  written out in the actual signature. This is exactly bijectivity of the sum map
  on those subspaces. The canonical map is linear, so bijectivity is equivalent to
  being a vector-space isomorphism. The existential uniqueness quantifies over the
  pair of ambient vectors, so no irrelevant choice of factorization is demanded.
- Trivial intersection as functors on every commutative k-algebra: `hinter` quantifies
  over `(R : Type u) [CommRing R] [Algebra k R]` and both R-points. Equal images
  `h ≫ i = t ≫ j` must equal `1` in the group of R-points of G. Conversely the
  identity belongs to both subgroup images since the inclusions are homomorphisms.
  Nonreduced test algebras are included; this is not merely an intersection of k-points.
- Multiplication H times_k K to G, (h,k) maps to hk:
  `((i ⊗ₘ j) ≫ μ[G]).left`, where the cartesian tensor in Over is the scheme
  pullback over Spec k, `i ⊗ₘ j` applies the two inclusions, and `μ[G]` is G's
  actual multiplication morphism. Conclusion: `IsOpenImmersion` of this morphism.
- Disconnected G, H, K are all allowed: there is no connectedness or irreducibility
  instance. No condition on the characteristic is present.

Recorded statement-dependency declarations used (full definitions and docstrings read):

- def-weil-field: `Field`, Mathlib.Algebra.Field.Defs.
- def-weil-algebraic-closure: `IsAlgClosed`, Mathlib.FieldTheory.IsAlgClosed.Basic;
  this is the algebraically closed clause of the node's Mathlib match.
- def-sc-group-scheme: `CategoryTheory.GrpObj`, Mathlib.CategoryTheory.Monoidal.Grp,
  specialized to Over (Spec k); `MonObj.mul` is the multiplication.
- def-sbc-smooth-morphisms: `AlgebraicGeometry.Smooth`,
  Mathlib.AlgebraicGeometry.Morphisms.Smooth.
- def-weil-finite-type-morphism: `AlgebraicGeometry.LocallyOfFiniteType`,
  Mathlib.AlgebraicGeometry.Morphisms.FiniteType, and `AlgebraicGeometry.QuasiCompact`,
  Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact.
- def-sc-group-scheme-subgroup: `AlgebraicGeometry.IsClosedSubgroupScheme`,
  WeilConjectures.AlgebraicGeometry.GroupScheme.Defs, extending `IsSubgroupScheme`.
- def-weil-open-immersion: `AlgebraicGeometry.IsOpenImmersion`,
  Mathlib.AlgebraicGeometry.OpenImmersion.
- def-sc-scheme-tangent-space: `AlgebraicGeometry.schemeTangentSpace` and its canonical
  additive instance, WeilConjectures.AlgebraicGeometry.SchemeTangentSpace.
- def-pc-fibre-product: `CategoryTheory.Limits.pullback`,
  Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback; the tensor-object instance
  in Mathlib.CategoryTheory.Monoidal.Cartesian.Over has this pullback as underlying scheme.
- The existing identity-point construction `AlgebraicGeometry.GrpObj.onePoint`,
  WeilConjectures.AlgebraicGeometry.GroupScheme.Basic, is used without making a copy.

The plain proof imports supply `HasRingHomProperty.Spec_iff` (RingHomProperties),
`Algebra.Smooth.baseChange` and `Algebra.Smooth.comp` (RingTheory.Smooth.Basic),
`IsOpenImmersion.of_flat_of_mono` (FlatMono), the etale characterizations (Etale),
`product_tangentSpace_directSum` (Sheaf.AlgebraicGeometry.ProductTangentSpaceDirectSum),
and `group_addition_tangent_differential`
(Sheaf.AlgebraicGeometry.GroupAdditionTangentDifferential). The public imports already
supply closed immersions, affine spectrum pullbacks and finite-type notions used by the
proof. The sole unstated proof dependency `lem-sfb-smooth-tangent-isomorphism-etale` has
no Lean record and hence no module to import; it is needed only for the postponed proof,
not for any object or hypothesis of this statement. Every proof step and its node names
are reproduced in the theorem docstring.

Edge cases checked before writing:

- H trivial, K=G, or vice versa: the unique decomposition is (0,v), respectively (v,0),
  and multiplication is the expected identity after product with Spec k.
- G zero-dimensional smooth (finite etale, possibly disconnected): all identity tangent
  spaces vanish, so hLie is satisfied and the conclusion correctly allows an open subset
  consisting of some components, not necessarily all of G.
- H=K=1 inside a positive-dimensional G: hLie fails; the false claim that a closed point
  is open in positive dimension is excluded by the stated Lie hypothesis.
- No empty group scheme can satisfy GrpObj over the nonempty Spec of a field, because
  the identity section exists. The zero-dimensional identity group remains included.
- Positive characteristic, infinitesimal test algebras, and arbitrary components are
  retained. For example a nontrivial infinitesimal intersection cannot escape hinter.
- The same explicit universe u is used for the base, schemes and all algebra tests,
  as in the recorded subgroup interface; no independent smaller test universe appears.

Searches run, with actual results:

1. msearch.py leanfinder: "Multiplication of smooth closed subgroup schemes with trivial
   intersection and complementary Lie algebras is an open immersion". Eight hits:
   IsOpen.isImmersionAtOfComplement; Manifold.IsImmersionOfComplement.prodMap;
   Manifold.IsImmersionAtOfComplement.prodMap; the two scheme coproduct open immersions;
   Algebra.FormallyUnramified.isOpenImmersion_SpecMap_lmul;
   Manifold.IsImmersion.prodMap; Manifold.IsImmersionOfComplement.isImmersion.
   None is the algebraic-group statement.
2. msearch.py loogle: "AlgebraicGeometry.IsOpenImmersion,
   AlgebraicGeometry.IsClosedSubgroupScheme". Zero hits, with diagnostic that the latter
   name is unknown to the external Mathlib search service (it is an upstream declaration).
3. msearch.py grep: `(transverse|[Cc]omplementary).*(subgroup|[Ll]ie)|
   ([Ll]ie|[Tt]angent).*([Oo]pen[Ii]mmersion)`. Two Mathlib hits, comments in
   GroupTheory/SemidirectProduct.lean:236 and GroupTheory/Complement.lean:39;
   neither concerns group schemes or open immersions.
4. msearch.py leansearch: "Smooth closed subgroup schemes with trivial functorial
   intersection and complementary tangent spaces have open immersion multiplication".
   Eight hits on formally unramified spectrum multiplication, open-immersion smoothness,
   analytic Lie-group multiplication and open-immersion composition; no exact statement.
5. rg across both lean/WeilConjectures and lean/Sheaf for the item id and transverse or
   complementary subgroup/Lie phrases found only unrelated comments; the exact chosen
   declaration name also has no occurrence. The prescribed grep for the item id in
   lean/WeilConjectures had no hits. The existing group/subgroup/tangent definitions were
   then opened directly and reused.

No STATEMENT-DISPUTED issue or source correction is needed. The inherited BLOCKED ending
was a stage-1 unchanged-split refusal; the current brief's stage-handoff rule specifically
permits this stage-2 work, and the queue contains this node at stage 2 with no Lean record.

Validation: scompile.py compiled the statement in sandbox and library-module modes cleanly.
The first pass exposed a missing public import of GroupScheme.Defs, which was added.
Only the one named theorem is postponed; no data or auxiliary proof is replaced by sorry.

## Second reading by Q62

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
