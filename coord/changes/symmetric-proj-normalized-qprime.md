# AlgebraicGeometry.SymmetricProjTautologicalCharts.normalized_pullback_generator_local_coefficients_qprime

## Reason

The previous Lean statement claimed the coefficient formula for an arbitrary morphism
`q' : M ⟶ D'.line`. This is false. For `E = k²` over a field, on the standard chart
of `P¹` where the tautological quotient is `(1,t)`, take `a = 1`, `c = (1,t)`
and the module morphism `q' = (0,1)`. The first basis vector forces `b' = 0`
and the second forces `1 = 0`. The cited Stacks Tags 01N2, 01NQ, 01NR and 01OB
provide compatibility of the normalized quotient, not of arbitrary morphisms.
The repaired declaration defines exactly the normalized map already used by the parent.

The module was unclaimed on the server at the start of this repair. No target
signature or definition changes. No arbitrary-map formula is needed by any caller.

## Old

```lean
theorem normalized_pullback_generator_local_coefficients_qprime
    {X S : Scheme.{u}} (g : X ⟶ S) (E : S.Modules) [E.IsQuasicoherent]
    [((Scheme.Modules.tensorPullback g).obj E).IsQuasicoherent]
    (D : ProjectiveBundleQuotientGeometry.TautologicalQuotient E)
    (D' : ProjectiveBundleQuotientGeometry.TautologicalQuotient
      ((Scheme.Modules.tensorPullback g).obj E))
    (b : Scheme.GradedAlgebraData.PullbackData g (SymmetricAlgebraSheaf.gradedAlgebraData E)
      (SymmetricAlgebraSheaf.gradedAlgebraData ((Scheme.Modules.tensorPullback g).obj E)))
    (hb : ∀ (U : S.affineOpens) (W : X.affineOpens) (h : W.1 ≤ g ⁻¹ᵁ U.1)
      (m : E.val.obj (op U.1)),
      b.map h (SymmetricAlgebra.ι Γ(S, U.1) _ m) =
        SymmetricAlgebra.ι Γ(X, W.1) _
          (((Scheme.Modules.tensorPullback g).obj E).presheaf.map (homOfLE h).op
            (Scheme.Modules.tensorPullbackSection g E U.1 m)))
    (e : (Scheme.Modules.tensorPullback
        (b.relProjComparison ≫ (SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom)).obj E =
      (Scheme.Modules.tensorPullback
        ((SymmetricAlgebraSheaf.gradedAlgebraData
          ((Scheme.Modules.tensorPullback g).obj E)).relProjHom ≫ g)).obj E) :
    let T := (SymmetricAlgebraSheaf.gradedAlgebraData
      ((Scheme.Modules.tensorPullback g).obj E)).relProj
    let M := (Scheme.Modules.tensorPullback
      (b.relProjComparison ≫ (SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom)).obj E
    let P := (Scheme.Modules.tensorPullback b.relProjComparison).obj D.line
    let q : M ⟶ P :=
      (Scheme.Modules.tensorPullbackSectionComp b.relProjComparison
        (SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom).hom.app E ≫
        (Scheme.Modules.tensorPullback b.relProjComparison).map D.quotient
    ∀ (q' : M ⟶ D'.line),
    ∀ (U : S.affineOpens) (W : T.Opens) (h : W ≤
      (b.relProjComparison ≫ (SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom) ⁻¹ᵁ U.1)
      (x : T) (Z : T.Opens) (hZW : Z ≤ W) (hx : x ∈ Z)
      (a : Γ(P, Z)) (c : Γ(E, U.1) → Γ(T, Z)),
      (∀ t : Γ(E, U.1),
        let s := M.presheaf.map (homOfLE (hZW.trans h)).op
          (Scheme.Modules.tensorPullbackSection
            (b.relProjComparison ≫ (SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom)
            E U.1 t)
        q.app Z s = c t • a) →
      ∃ (b' : Γ(D'.line, Z)),
        ∀ t : Γ(E, U.1),
          let s := M.presheaf.map (homOfLE (hZW.trans h)).op
            (Scheme.Modules.tensorPullbackSection
              (b.relProjComparison ≫ (SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom)
              E U.1 t)
          q'.app Z s = c t • b'
```

## New

```lean
theorem normalized_pullback_generator_local_coefficients_qprime
    {X S : Scheme.{u}} (g : X ⟶ S) (E : S.Modules) [E.IsQuasicoherent]
    [((Scheme.Modules.tensorPullback g).obj E).IsQuasicoherent]
    (D : ProjectiveBundleQuotientGeometry.TautologicalQuotient E)
    (D' : ProjectiveBundleQuotientGeometry.TautologicalQuotient
      ((Scheme.Modules.tensorPullback g).obj E))
    (b : Scheme.GradedAlgebraData.PullbackData g (SymmetricAlgebraSheaf.gradedAlgebraData E)
      (SymmetricAlgebraSheaf.gradedAlgebraData ((Scheme.Modules.tensorPullback g).obj E)))
    (hb : ∀ (U : S.affineOpens) (W : X.affineOpens) (h : W.1 ≤ g ⁻¹ᵁ U.1)
      (m : E.val.obj (op U.1)),
      b.map h (SymmetricAlgebra.ι Γ(S, U.1) _ m) =
        SymmetricAlgebra.ι Γ(X, W.1) _
          (((Scheme.Modules.tensorPullback g).obj E).presheaf.map (homOfLE h).op
            (Scheme.Modules.tensorPullbackSection g E U.1 m)))
    (e : (Scheme.Modules.tensorPullback
        (b.relProjComparison ≫ (SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom)).obj E =
      (Scheme.Modules.tensorPullback
        ((SymmetricAlgebraSheaf.gradedAlgebraData
          ((Scheme.Modules.tensorPullback g).obj E)).relProjHom ≫ g)).obj E) :
    let T := (SymmetricAlgebraSheaf.gradedAlgebraData
      ((Scheme.Modules.tensorPullback g).obj E)).relProj
    let M := (Scheme.Modules.tensorPullback
      (b.relProjComparison ≫ (SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom)).obj E
    let P := (Scheme.Modules.tensorPullback b.relProjComparison).obj D.line
    let q : M ⟶ P :=
      (Scheme.Modules.tensorPullbackSectionComp b.relProjComparison
        (SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom).hom.app E ≫
        (Scheme.Modules.tensorPullback b.relProjComparison).map D.quotient
    let q' : M ⟶ D'.line := (eqToIso e).hom ≫
      (Scheme.Modules.tensorPullbackSectionComp
        (SymmetricAlgebraSheaf.gradedAlgebraData
          ((Scheme.Modules.tensorPullback g).obj E)).relProjHom g).hom.app E ≫ D'.quotient
    ∀ (U : S.affineOpens) (W : T.Opens) (h : W ≤
      (b.relProjComparison ≫ (SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom) ⁻¹ᵁ U.1)
      (x : T) (Z : T.Opens) (hZW : Z ≤ W) (hx : x ∈ Z)
      (a : Γ(P, Z)) (c : Γ(E, U.1) → Γ(T, Z)),
      (∀ t : Γ(E, U.1),
        let s := M.presheaf.map (homOfLE (hZW.trans h)).op
          (Scheme.Modules.tensorPullbackSection
            (b.relProjComparison ≫ (SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom)
            E U.1 t)
        q.app Z s = c t • a) →
      ∃ (b' : Γ(D'.line, Z)),
        ∀ t : Γ(E, U.1),
          let s := M.presheaf.map (homOfLE (hZW.trans h)).op
            (Scheme.Modules.tensorPullbackSection
              (b.relProjComparison ≫ (SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom)
              E U.1 t)
          q'.app Z s = c t • b'
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.SymmetricProjPullbackGeneratorLocalCoefficientsQPrime | unclaimed | Restrict the false arbitrary-map statement to the normalized map. Retain its existing proof hole. |
| Sheaf.AlgebraicGeometry.SymmetricProjPullbackGeneratorLocalCoefficients | C4 | Only direct importer and only consumer; prove its unchanged statement by applying the corrected lemma to the local data from the q lemma. |

A search of all transitive importers finds no other mention of the changed declaration.
The public imports stay unchanged. The direct importer is compiled after the repaired
module in the same sandbox. Further targets depend on the unchanged parent interface.
The only DAG citer is `lem-trf-symmetric-proj-pullback-generator-local-coefficients`;
its normalized-map use still holds, as recorded in `statement_change`.

## Status

landed 20261028T055624-L-779065 2026-10-28 (merge of deliver/C4/Sheaf.AlgebraicGeometry.SymmetricProjPullbackGeneratorLocalCoefficients)
