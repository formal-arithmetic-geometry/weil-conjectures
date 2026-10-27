## Worker report

The module states `AlgebraicGeometry.affine_commutative_extension_pushout`; its only postponed proof is this theorem. Four helper definitions supply the existing additive group with a `Grp` bundle, the explicit antidiagonal scheme map, and the two product inclusions. Their data are actual maps, without postponed data or arbitrary choices. The antidiagonal is identified with a group homomorphism `a` by the equality `a.hom.hom = affineExtensionAntidiagonal i φ`; thus neither its map nor the quotient is arbitrary. No statement correction or new node is needed. The landed definition node `def-sfb-fppf-group-quotient-presentation` is added to stmt_deps because it owns `AlgebraicGeometry.IsFppfGroupQuotient`, the plain Prop-valued quotient presentation used in the statement. The theorem node `lem-sfb-affine-normal-quotient-geometry` remains a proof dependency only.

Hypotheses, clause by clause:

- A field k is `{k : Type u} [Field k]`. All schemes and test schemes use the same bounded universe u; no independent lower universe or characteristic restriction occurs.
- N,B,Q are `Grp (Over (Spec (.of k)))`; the three `IsCommMonObj` instances assert commutativity. Morphisms i,q,φ are bundled group homomorphisms, so no extra multiplicativity hypotheses or private group notions are used.
- Affineness is each `IsAffine X.X.left`. Finite type is `LocallyOfFiniteType X.X.hom` together with `QuasiCompact X.X.hom`, for X=N,B,Q.
- The closed kernel embedding is `[IsClosedSubgroupScheme i.hom.hom]` and `hqker : IsPullback i.hom.hom (toUnit N.X) q.hom.hom η[Q.X]`. This identifies the actual inclusion with the scheme-theoretic kernel, on all test algebras.
- Faithful flatness of q is the ring-map condition `q.hom.hom.left.appTop.hom.FaithfullyFlat`. The affine coordinate map has the reversed direction required by the source. `hqfp` is `LocallyOfFinitePresentation q.hom.hom.left`; for these affine schemes this is global finite presentation. These are exactly the node's q hypotheses.
- The given map to Gₐ is `φ : N ⟶ affineExtensionAdditive k`, using the existing standard additive group law.

Conclusions, clause by clause:

- The image J is specified through the closed antidiagonal embedding a, whose underlying map is `lift i.hom.hom (φ.hom.hom ≫ ι[(affineExtensionAdditive k).X])`. In multiplicative notation for group objects this is exactly (i(n),-φ(n)). Closedness is `IsClosedImmersion a.hom.hom.left`; since a is a group homomorphism this is the required closed subgroup embedding.
- The existential E has `IsCommMonObj E.X`, `IsAffine E.X.left`, `LocallyOfFiniteType E.X.hom`, and `QuasiCompact E.X.hom`. The actual quotient is `IsFppfGroupQuotient a ρ`. Reading its existing definition in full: its kernel square is scheme-theoretic, its coset presheaf is the coequalizer of projection and right translation by a, and the universal arrow to the representable E is its fppf sheafification. On an affine k-algebra R this is exactly (B(R) × R)/J(R). Its topology is the actual `Scheme.fppfTopology.over (Spec (.of k))`.
- The required quotient-map properties are `ρ.hom.hom.left.appTop.hom.FaithfullyFlat` and `LocallyOfFinitePresentation ρ.hom.hom.left`. The equivalent geometric `Flat` and `Surjective` properties are also explicit.
- b(x)=ρ(x,0) and j(t)=ρ(0,t) are written without opaque statement-local lets: `affineExtensionLeftInclusion B ≫ ρ` and `affineExtensionRightInclusion B ≫ ρ`. The definitions use `lift (𝟙 B.X) (toUnit B.X ≫ η[...])` and `lift (toUnit ... ≫ η[B.X]) (𝟙 _)`, respectively.
- q' is induced by q on the first product factor: `ρ ≫ q' = fst B (affineExtensionAdditive k) ≫ q`.
- Exactness in the same scheme-theoretic sense is the closed subgroup property for j, its displayed `IsPullback` kernel square, and faithful flatness and finite presentation of q'. Flatness and surjectivity of q' are also explicit.
- bi=jφ is `i ≫ affineExtensionLeftInclusion B ≫ ρ = φ ≫ affineExtensionRightInclusion B ≫ ρ`. q'b=q is `affineExtensionLeftInclusion B ≫ ρ ≫ q' = q`.
- The represented commutative fppf pushout property quantifies every `H : Grp (Over (Spec (.of k)))` with `[IsCommMonObj H.X]`, and every pair f,g with `i ≫ f = φ ≫ g`. It asserts a unique homomorphism h with the two required composites. H is not assumed affine, finite type, smooth or connected. Yoneda and subcanonicity identify these with maps between represented fppf sheaves of commutative groups, exactly the node's asserted pushout category. This does not silently replace that clause with a pushout of schemes.
- All product symbols are the cartesian tensor products in `Over (Spec (.of k))`, hence fibre products over Spec k.

Dependency declarations read and used:

- `Field` (Mathlib.Algebra.Field.Defs).
- `CategoryTheory.GrpObj`, `CategoryTheory.Grp`, `CategoryTheory.IsCommMonObj`, `CategoryTheory.IsMonHom` (Mathlib.CategoryTheory.Monoidal.Grp and Mon); these are the declarations recorded for def-sc-group-scheme, with their signatures and group-object conventions read in the source.
- `AlgebraicGeometry.IsSubgroupScheme`, `IsClosedSubgroupScheme`, `IsNormalSubgroupScheme` (WeilConjectures.AlgebraicGeometry.GroupScheme.Defs), including the all-algebra-point injectivity and the closed-immersion field.
- `AlgebraicGeometry.StandardGroupSchemes.additive`, `additiveGroup` and the prescribed comultiplication/counit/antipode (Sheaf.AlgebraicGeometry.StandardGroupSchemes). The helper `affineExtensionAdditive` only bundles that exact object and law.
- `AlgebraicGeometry.LocallyOfFiniteType` and `QuasiCompact` (Mathlib.AlgebraicGeometry.Morphisms.FiniteType and QuasiCompact), and `Spec`/`Spec.map` (Mathlib.AlgebraicGeometry.Scheme).
- `CategoryTheory.Limits.pullback`, its projections and universal property (Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback). The group-object kernel declaration and docstring were read in WeilConjectures.Mathlib.CategoryTheory.Monoidal.Cartesian.Grp.
- `AlgebraicGeometry.IsFppfGroupQuotient` (Sheaf.AlgebraicGeometry.GroupScheme.AffineNormalQuotientGeometry), owned by `def-sfb-fppf-group-quotient-presentation` (Q95, existing:true). This definition supplies the statement interface. The theorem `affine_normal_quotient_geometry` from the same module is used only by the proof plan, through the existing proof dependency `lem-sfb-affine-normal-quotient-geometry`.

The theorem docstring contains all six DAG proof steps: antidiagonal coordinate surjectivity, affine normal quotient, induced q' and identities, kernel identification by local lifts and descent, the two-sided quotient comparison proving q' fppf, and the sheafification pushout universal property. Stated proof dependencies are imported. The faithfully-flat group-quotient universal-property node has no Lean record or Mathlib match in the read clone, so it contributes no import. No declaration of that proof-only node is needed to type this statement.

Sources read: Milne iAG2017, printed pp.101--103 (Theorem 5.13 and Proposition 5.18) and p.296 (the exact pushout diagram in the proof of Proposition 14.48), extracted from the local PDF. The diagram is precisely the source construction used here.

Edge cases checked before writing: N=0 gives E=B×Gₐ; φ=0 gives Q×Gₐ; B=N=Gₐ with φ=id gives E=Gₐ and the bottom quotient is the zero group. In characteristic 2 the inverse is still the prescribed additive inverse, so the sign is handled uniformly. N=αₚ tests a nonreduced subgroup: the kernel square and quotient statement concern all algebra-valued points, not only field-valued points. There is no smoothness, reducedness or perfect-field hypothesis. The empty test scheme (zero ring) is retained by the over-category formulation. No statement is disputed.

Searches:

- `msearch.py Q96 ... leanfinder "Pushout of an extension of commutative affine algebraic groups along a homomorphism of its kernel to the additive group is represented by an affine group scheme"`: eight general affine scheme/morphism hits, none stating this result.
- `msearch.py Q96 ... loogle "CategoryTheory.IsPushout, CategoryTheory.Grp, AlgebraicGeometry.IsClosedSubgroupScheme"`: zero hits; the project-only subgroup declaration is unknown to Loogle.
- `msearch.py Q96 ... grep "pushout|Pushout" AlgebraicGeometry/Group`: zero Mathlib hits.
- `rg` in lean/WeilConjectures and lean/Sheaf for extension pushouts found SplitTorusCharacterPushout, whose kernel is a split torus and whose target is Gₘ, with additional smoothness hypotheses and frame data. It does not state the present additive affine pushout. The existing affine normal quotient interface is suitable for reuse.
- Search for the node id in lean/WeilConjectures: no match. Search for each of the five proposed declaration names in Mathlib, lean/WeilConjectures and lean/Sheaf: no match.

Validation: server compilation through scompile.py succeeded after replacing a bundled-product subgroup elaboration with the equivalent closed-immersion condition on its homomorphism; the only subsequent finding was a line over 100 columns, now wrapped. The final dry run recompiles the completed delivery.

## Second reading by Q96

No independent worker second reading: this dispatcher assignment explicitly prohibits starting agents. The maintainer independently reviews the delivery. I did reread the final node and signature against every clause above. That rereading removed statement-local lets, retained nonaffine represented targets H, and included j's closed subgroup property explicitly. No mathematical hypothesis was added, no conclusion dropped, and no node correction was required.

## Repair of returned delivery 7bb962710f6a

H2: Replaced the added theorem statement dependency `lem-sfb-affine-normal-quotient-geometry` with the landed definition node `def-sfb-fppf-group-quotient-presentation`, whose existing:true record owns exactly `AlgebraicGeometry.IsFppfGroupQuotient`. Read its current live node and the full definition at AffineNormalQuotientGeometry.lean:60: the kernel square, local surjectivity, sheaf condition, torsor isomorphism and sheafification universal arrow are the interface used here. The theorem node remains in proof_deps, as required by the six-step proof plan. Compared the sandbox node with current main: all fields other than lean and the single added stmt_dep agree. Kept the Lean module and the complete lean record unchanged from the returned delivery. The delivery wrapper rebases this repaired packet on current live main before preflight and push.

H11 advisory: the section above explicitly describes a self-reread, not an independent worker review. No other agent was started; the dispatcher prohibits it, and the maintainer supplies the independent review. The returned independent review already checked all mathematical clauses, universes and edge cases.
