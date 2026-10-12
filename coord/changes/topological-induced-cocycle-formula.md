# CategoryTheory.topological_induced_cocycle_formula

## Reason

The old Lean theorem is false: it constrains an arbitrary `edge` by the resolution
comparison, without any hypothesis identifying that edge. For the identity map on
one point, choose the zero edge and a nonzero degree-zero class. The asserted formula
would make this nonzero class zero. The source constructs the edge instead.

The repair fixes `a` with its generator equation and existentially constructs a
compatible edge. It follows the same resolution comparison and naturality route.
No target statement, and no definition appearing in a target, changes. The original
false universal-edge claim is not counted as an unchanged statement proved.

## Old

```lean
theorem topological_induced_cocycle_formula {Z X : TopCat.{u}} (f : Z ⟶ X) [(TopCat.Sheaf.pushforwardAb f).Additive] (HX : ℕ → (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} ⥤ AddCommGrpCat.{u})) (HZ : ℕ → (Sheaf (Opens.grothendieckTopology Z) AddCommGrpCat.{u} ⥤ AddCommGrpCat.{u})) (hX : ∀ n, HX n = Sheaf.cohomologyPresheafFunctor (Opens.grothendieckTopology X) n ⋙ (evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj (op ⊤)) (hZ : ∀ n, HZ n = Sheaf.cohomologyPresheafFunctor (Opens.grothendieckTopology Z) n ⋙ (evaluation (Opens Z)ᵒᵖ AddCommGrpCat.{u}).obj (op ⊤)) (edge : ∀ p : ℕ, TopCat.Sheaf.pushforwardAb f ⋙ HX p ⟶ HZ p) (a : (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj (yoneda.obj (⊤ : Opens X) ⋙ AddCommGrpCat.free) ⟶ (TopCat.Sheaf.pushforwardAb f).obj ((presheafToSheaf (Opens.grothendieckTopology Z) AddCommGrpCat.{u}).obj (yoneda.obj (⊤ : Opens Z) ⋙ AddCommGrpCat.free))) (ha : ∀ (U : Opens X) (h : U ⟶ (⊤ : Opens X)), a.hom.app (op U) ((toSheafify (Opens.grothendieckTopology X) (yoneda.obj (⊤ : Opens X) ⋙ AddCommGrpCat.free)).app (op U) (FreeAbelianGroup.of h)) = (toSheafify (Opens.grothendieckTopology Z) (yoneda.obj (⊤ : Opens Z) ⋙ AddCommGrpCat.free)).app (op ((Opens.map f).obj U)) (FreeAbelianGroup.of ((Opens.map f).map h ≫ eqToHom (Opens.map_top f)))) : ∀ (F : Sheaf (Opens.grothendieckTopology Z) AddCommGrpCat.{u}) (I : InjectiveResolution F) (J : InjectiveResolution ((TopCat.Sheaf.pushforwardAb f).obj F)) (φ : J.cocomplex ⟶ ((TopCat.Sheaf.pushforwardAb f).mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex) (_hφ : J.ι.f 0 ≫ φ.f 0 = (TopCat.Sheaf.pushforwardAb f).map (I.ι.f 0)) (p : ℕ) (s : (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj (yoneda.obj (⊤ : Opens X) ⋙ AddCommGrpCat.free) ⟶ J.cocomplex.X p) (hs : s ≫ J.cocomplex.d p (p + 1) = 0) (z : (presheafToSheaf (Opens.grothendieckTopology Z) AddCommGrpCat.{u}).obj (yoneda.obj (⊤ : Opens Z) ⋙ AddCommGrpCat.free) ⟶ I.cocomplex.X p) (hz : z ≫ I.cocomplex.d p (p + 1) = 0) (_hsz : a ≫ (TopCat.Sheaf.pushforwardAb f).map z = s ≫ φ.f p), (eqToHom (congrArg (fun Q ↦ Q.obj F) (hZ p))) ((edge p).app F ((eqToHom (congrArg (fun Q ↦ Q.obj ((TopCat.Sheaf.pushforwardAb f).obj F)) (hX p)).symm) (J.extMk s (p + 1) rfl hs))) = I.extMk z (p + 1) rfl hz
```

## New

```lean
theorem topological_induced_cocycle_formula {Z X : TopCat.{u}} (f : Z ⟶ X) [(TopCat.Sheaf.pushforwardAb f).Additive] (HX : ℕ → (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} ⥤ AddCommGrpCat.{u})) (HZ : ℕ → (Sheaf (Opens.grothendieckTopology Z) AddCommGrpCat.{u} ⥤ AddCommGrpCat.{u})) (hX : ∀ n, HX n = Sheaf.cohomologyPresheafFunctor (Opens.grothendieckTopology X) n ⋙ (evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj (op ⊤)) (hZ : ∀ n, HZ n = Sheaf.cohomologyPresheafFunctor (Opens.grothendieckTopology Z) n ⋙ (evaluation (Opens Z)ᵒᵖ AddCommGrpCat.{u}).obj (op ⊤)) (a : (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj (yoneda.obj (⊤ : Opens X) ⋙ AddCommGrpCat.free) ⟶ (TopCat.Sheaf.pushforwardAb f).obj ((presheafToSheaf (Opens.grothendieckTopology Z) AddCommGrpCat.{u}).obj (yoneda.obj (⊤ : Opens Z) ⋙ AddCommGrpCat.free))) (ha : ∀ (U : Opens X) (h : U ⟶ (⊤ : Opens X)), a.hom.app (op U) ((toSheafify (Opens.grothendieckTopology X) (yoneda.obj (⊤ : Opens X) ⋙ AddCommGrpCat.free)).app (op U) (FreeAbelianGroup.of h)) = (toSheafify (Opens.grothendieckTopology Z) (yoneda.obj (⊤ : Opens Z) ⋙ AddCommGrpCat.free)).app (op ((Opens.map f).obj U)) (FreeAbelianGroup.of ((Opens.map f).map h ≫ eqToHom (Opens.map_top f)))) : ∃ edge : ∀ p : ℕ, TopCat.Sheaf.pushforwardAb f ⋙ HX p ⟶ HZ p, ∀ (F : Sheaf (Opens.grothendieckTopology Z) AddCommGrpCat.{u}) (I : InjectiveResolution F) (J : InjectiveResolution ((TopCat.Sheaf.pushforwardAb f).obj F)) (φ : J.cocomplex ⟶ ((TopCat.Sheaf.pushforwardAb f).mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex) (_hφ : J.ι.f 0 ≫ φ.f 0 = (TopCat.Sheaf.pushforwardAb f).map (I.ι.f 0)) (p : ℕ) (s : (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj (yoneda.obj (⊤ : Opens X) ⋙ AddCommGrpCat.free) ⟶ J.cocomplex.X p) (hs : s ≫ J.cocomplex.d p (p + 1) = 0) (z : (presheafToSheaf (Opens.grothendieckTopology Z) AddCommGrpCat.{u}).obj (yoneda.obj (⊤ : Opens Z) ⋙ AddCommGrpCat.free) ⟶ I.cocomplex.X p) (hz : z ≫ I.cocomplex.d p (p + 1) = 0) (_hsz : a ≫ (TopCat.Sheaf.pushforwardAb f).map z = s ≫ φ.f p), (eqToHom (congrArg (fun Q ↦ Q.obj F) (hZ p))) ((edge p).app F ((eqToHom (congrArg (fun Q ↦ Q.obj ((TopCat.Sheaf.pushforwardAb f).obj F)) (hX p)).symm) (J.extMk s (p + 1) rfl hs))) = I.extMk z (p + 1) rfl hz
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Topology.TopologicalInducedCocycleFormula | H3 | Intermediate signature corrected; reduced to objectwise comparison and naturality. |
| Sheaf.Topology.TopologicalInducedCohomologyCocycle | unclaimed | Forced proof-only adaptation; its entire existing signature and visibility stay identical. |

The downstream scan finds 623 transitive importers, but only the latter module uses
this declaration. All other downstream statements remain unchanged. The parent node
already had the source's existential statement, which the adapted proof still proves.
Its proof record is updated to match the two declarations actually used.

The forced changed lines are 103-106 of the original caller: ignore the unconstrained
edge witness when obtaining `a`; obtain the compatible edge from the repaired theorem;
assemble the same existential conclusion. No caller imports or other lines change.
The original caller compiles against the old dependency but fails against the repaired
one at line 106 with `Application type mismatch`: the argument `edge` has type
`(p : ℕ) → TopCat.Sheaf.pushforwardAb f ⋙ HX p ⟶ HZ p`, where the new application expects
`a : KX ⟶ f_*KZ`. The adapted caller compiles against the repaired dependency.

## Status

landed 20261012T173834-L-3297854 2026-10-12 (merge of deliver/H3/Sheaf.Topology.TopologicalInducedCocycleFormula)
