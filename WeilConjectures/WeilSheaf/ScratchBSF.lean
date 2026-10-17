module
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.UniversalCoverLift
public import WeilConjectures.SixFunctors.ProEtale.Adic.LisseMonodromyLift
public import WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryGenericPoint
public import WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryGenericPath
public import WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryGenericRep
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.GermLowerStar
public import WeilConjectures.WeilSheaf.StalkTransportGeneral
public import WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryNeighbourhoodData
public import WeilConjectures.WeilSheaf.BoundaryStalkFrobenius
public import WeilConjectures.WeilSheaf.BoundaryStalkSpecialization
public import WeilConjectures.SixFunctors.ProEtale.StrictlyHenselianNeighbourhood
public import WeilConjectures.WeilSheaf.StalkStrictlyHenselian
public import WeilConjectures.SixFunctors.ProEtale.Adic.LisseGaloisDescent
public import WeilConjectures.WeilSheaf.BoundaryStalkGaloisInvariants
public import WeilConjectures.RingTheory.StrictlyHenselianInvariants
public import WeilConjectures.RingTheory.InertiaStrictHenselization
public import WeilConjectures.RingTheory.ProEtale.IndEtaleDirectedUnion
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let all := env.constants.toList.map (·.1.toString)
  for n in ["Algebra.IndEtale.of_directedOn","BoundaryNeighbourhood","IsAdicLisseSheaf.exists_map_fieldExtHom_eq","IsAdicLisseSheaf.injective_map_fieldExtHom","Polynomial.eq_of_isRoot_of_sub_mem_maximalIdeal","`φ_n`.","atPrimeMap_mul","atPrimeMap_one","atPrimeMap_sub_mem_maximalIdeal","bijective_germ_of_weaklyEtale_of_isStrictlyHenselianLocalRing","bijective_germ_stalk_directImage","cocone_setDiag_eq","coe_frobenius_symm_pow","comp_map_comp_eq_of_compatible","comp_transport_liftPath","constantCoverPoint","constantCoverPoint_injective","constantCoverPoint_left","counit_frobeniusStr_compatible","downAut_ofLift","eq_overLift","exists_algEquiv_comp_specMap_eq","exists_comp_eq_of_weaklyEtale_of_surjective","exists_hom_of_isStrictlyHenselianLocalRing","exists_injective_stalk_directImage_range_eq_invariants","exists_mem_of_mem₂","exists_stalk_directImage_linearMap_invariants","fiber_map_arithmeticFrobenius_constantCoverPoint","fieldExtAut","fieldExtAut_comp_fieldExtHom","fieldExtHom","fieldExtObj","fixingSubgroup_fixedField_inertia","galoisToAut_constantCoverPoint","galois_comp_genericStructHom","genericBasePoint","genericBasePoint_comp","genericEmb","genericEmb_algebraMap","genericEmb_comp_algebraMap","genericEmb_galois","genericGeomPoint","genericGeomPoint_geometricFiberProj","genericGeomPoint_geometricFiberToAlgebraicClosure","genericSpecialization","genericSpecialization_frobenius","genericStalkEquiv","genericStalkEquiv_apply","genericStalkEquiv_fundamentalRep","genericStalkEquiv_fundamentalRep_of_deg_zero","genericStructHom","geomAut_ofLift","geometricFrobenius_pow_constantCoverPoint","geometricFrobenius_pow_path","germ_comp_lowerStar","germ_diagLift_comp_genericSpecialization","germ_eq_of_forall_map_fieldExtAut_eq","globalSectionsTransport_comp_resOver","globalSectionsTransport_frobeniusPowStr_comp'","globalSectionsTransport_frobeniusPowStr_comp_upperStar","globalSectionsTransport_frobeniusPowStr_one_comp_upperStar","globalSectionsTransport_refl_eq","henselianLocalRing_subring","inertiaAtPrimeAction","isClosed_inertia_integralClosure","isIso_liftRes_app","isLocalRing_subring","isStrictlyHenselianLocalRing_fixedPoints_atPrime","isStrictlyHenselianLocalRing_subring","isUnit_subring_iff","liftPath","liftPathHom","liftPath_hom_app_left","liftPath_map","liftPath_pt","liftRes","liftStalkIso","liftStalkIso_globalSectionsTransport","liftStalkIso_resOver","map_fieldExtAut_map_fieldExtHom","mem_maximalIdeal_subring_iff","nbhdGenericPoint","nbhdGenericPoint_comp","ofLift","overLift_nbhdGenericPoint_comp_pullbackComp","ptRes_app_comp_liftStalkIso_hom","pullbackPathIso'","pullbackPathIso'_comp","pullbackPathIso'_congr","pullbackPathIso'_eq","pullbackPathIso'_hom_app_left","pullbackPathIso'_liftPath_specMap","pullbackPathIso'_pullbackPathIso'_of_comp_eq","pullbackPathIso'_symm","pullbackPathIso'_trans","resOver_comp_globalSectionsTransport","setColimitPresentation","setDescAlgHom","setDescFun","setDescFun_eq","setDiag","smul_mem_maximalIdeal_iff","specFieldMap","specMap_algEquiv_comp_specFieldMap","specMap_comp_genericGeomPoint","spec_genericStructHom","stalkAt_frobenius_apply","stalk_frobenius_apply","stalk_frobenius_apply_eq","stalk_frobenius_intertwine","stalk_frobenius_intertwine_of_comp_eq","universalCover_transport_symm","upperStarHom","upperStarHom_counit","upperStarHom_frobeniusStr_compatible"] do
    match all.find? (fun s => s == n || s.endsWith ("." ++ n)) with
    | none => logInfo m!"MISSING {n}"
    | some s =>
      let nm := s.toName
      let axs ← liftCoreM <| Lean.collectAxioms nm
      if axs.contains ``sorryAx then logInfo m!"SORRY {s}"
