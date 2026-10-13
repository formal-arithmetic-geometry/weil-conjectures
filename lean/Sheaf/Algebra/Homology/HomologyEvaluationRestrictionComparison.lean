module

public import Sheaf.Algebra.Homology.HomologyEvaluationDefinitions

/-! # Restriction of cycle evaluation -/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace CategoryTheory

/-- Restriction transports evaluation to a cycle-compatible evaluation on the over site.

Source: Stacks Project, Tags 0A8X (Hom differential) and 08DL (open restriction).
(blueprint: new-e3-homology-evaluation-restriction-comparison).

Proof: Write F for restriction to V followed by restriction to the site over W.
Both restrictions are exact and preserve products. Construct the comparison
F(Hom(T,J)) to Hom(F(T),F(J)) degreewise using the product universal property
and the local internal-Hom identifications: each local map is sent to the same
map on the smaller open. Checking each product projection proves differential
compatibility and evaluation compatibility. Exactness gives comparisons on
cycles and homology; internal Hom commutes with these restrictions by the same
local-map identification. These give a and b. Define g by transporting F(e)
along a and b. On Hom cycles, the differential identity says evaluation on a
source cycle is a target cycle. The kernel property of target cycles therefore
gives d. Its composite with target cycle inclusion is the first displayed
identity. To prove the second, evaluate on sections of source cycles on every
slice open. The hypothesis he identifies g on these representatives with the
class of the target cycle just constructed. Extensionality of local linear
maps and separatedness give the second morphism identity. The definition of g
gives the last square. This uses neither K-injectivity nor a roof, and works
for zero complexes and empty opens by the same universal properties. -/
theorem homologyEvaluation_restriction_comparison (X : Scheme.{u})
    (T J : CochainComplex X.Modules ℤ) (n : ℤ)
    (e : (homComplex (R := X.sheaf) T J).homology n ⟶
      SheafOfModules.homObj (R := X.sheaf) (T.homology (-n)) (J.homology 0))
    (he : IsHomologyEvaluation X T J n e) (V : X.Opens) (W : V.toScheme.Opens) :
    let A := (moduleOpenOverComplexFunctor X V W).obj T
    let K := (moduleOpenOverComplexFunctor X V W).obj J
    let Q := homComplex (R := V.toScheme.sheaf.over W) A K
    let π := (Classical.choose
      (homComplex_projections_exists (R := V.toScheme.sheaf.over W)))
      A K n (-n) 0 (by omega)
    ∃ a : ((Scheme.Modules.restrictFunctor V.ι).obj
        ((homComplex (R := X.sheaf) T J).homology n)).over W ≅ Q.homology n,
      ∃ b : ((Scheme.Modules.restrictFunctor V.ι).obj
          (SheafOfModules.homObj (R := X.sheaf)
            (T.homology (-n)) (J.homology 0))).over W ≅
          SheafOfModules.homObj (R := V.toScheme.sheaf.over W)
            (A.homology (-n)) (K.homology 0),
        ∃ g : Q.homology n ⟶ SheafOfModules.homObj (R := V.toScheme.sheaf.over W)
            (A.homology (-n)) (K.homology 0),
          ∃ d : Q.cycles n ⟶ SheafOfModules.homObj (R := V.toScheme.sheaf.over W)
              (A.cycles (-n)) (K.cycles 0),
            d ≫ SheafOfModules.homObjMap (R := V.toScheme.sheaf.over W)
                (𝟙 _) (K.iCycles 0) =
              Q.iCycles n ≫ π ≫ SheafOfModules.homObjMap
                (R := V.toScheme.sheaf.over W) (A.iCycles (-n)) (𝟙 _) ∧
            d ≫ SheafOfModules.homObjMap (R := V.toScheme.sheaf.over W)
                (𝟙 _) (K.homologyπ 0) =
              Q.homologyπ n ≫ g ≫ SheafOfModules.homObjMap
                (R := V.toScheme.sheaf.over W) (A.homologyπ (-n)) (𝟙 _) ∧
            (((Scheme.Modules.restrictFunctor V.ι).map e).over W) ≫ b.hom =
              a.hom ≫ g := by
  sorry

end CategoryTheory
