# SheafOfModules.StrictScalarHom.CoefficientExtensionAssociators

## Reason

The complete unchanged-record proof repeatedly exceeds the 60-second compiler
limit. Profiling isolated large dependent record types and their repeated
checking. The repair shares each of the 24 long proposition fields as a named
transparent law definition and removes five redundant inverse proof fields
from `CoefficientExtensionAssociators`. The same inverse formulas are proved
from the retained forward formulas and isomorphism identities under the same
public getter names. No mathematical condition is dropped.

This is a definition repair in the held Sheaf module. The source-library tree,
all target declaration texts, and public imports are unchanged. The item theorem
is also fully proved: one original hole closed, zero added. No file is split.

## Old

The following are the original four records, verbatim:

```lean
structure NormalizedCoefficientCompatibility
    {R S R' S' : Sheaf J CommRingCat.{max c v u}}
    {φ : R ⟶ S} {a : R ⟶ R'} {b : S ⟶ S'} {φ' : R' ⟶ S'}
    {D : NormalizedCoefficientMaps.{c, v, u} φ}
    {Da : NormalizedCoefficientMaps.{c, v, u} a}
    {Db : NormalizedCoefficientMaps.{c, v, u} b}
    {D' : NormalizedCoefficientMaps.{c, v, u} φ'}
    (Q : NormalizedCoefficientSquare.{c, v, u} D Da Db D') : Prop where
  /-- The tensor coefficient map is the expected map on all local generators. -/
  tensor_pure : ∀ (A : Complex.{c, v, u} R) (n : ℤ) (V : Cᵒᵖ)
    (r : R'.obj.obj V) (s : S.obj.obj V) (x : (A.X n).val.obj V),
    (((Q.tensorComparison A).f n).val.app V)
        (Da.extension.section ((tensor.{c, v, u} φ).obj A) n V r
          (tensorSection.{c, v, u} φ A n V s x)) =
      tensorSection.{c, v, u} φ' (Da.extension.complex.obj A) n V
        (φ'.hom.app V r * b.hom.app V s) (Da.extension.section A n V 1 x)
  /-- Nu commutes with the canonical coefficient maps. -/
  nu : ∀ (A : Complex.{c, v, u} R),
    Q.tensorComparison A ≫ (D'.chains.nu.app (Da.extension.complex.obj A)).hom =
      Da.extension.complex.map (D.chains.nu.app A).hom ≫
        Q.restrictionMate.app (D.extension.complex.obj A) ≫
        (restriction.{c, v, u} φ').map (Q.extensionIso.app A).hom
  /-- Theta commutes with the canonical Hom comparisons and the restriction mate. -/
  theta : ∀ (P : Complex.{c, v, u} R) (N : Complex.{c, v, u} S),
    Da.extension.complex.map (D.chains.theta P N).hom ≫
        Da.homComparison P ((restriction.{c, v, u} φ).obj N) ≫
        homMap.{c, v, u} (𝟙 (Da.extension.complex.obj P)) (Q.restrictionMate.app N) =
      Q.restrictionMate.app (homComplex (R := S) (D.extension.complex.obj P) N) ≫
        (restriction.{c, v, u} φ').map (Db.homComparison (D.extension.complex.obj P) N) ≫
        (restriction.{c, v, u} φ').map (homMap.{c, v, u} (Q.extensionIso.app P).inv
          (𝟙 (Db.extension.complex.obj N))) ≫
        (D'.chains.theta (Da.extension.complex.obj P) (Db.extension.complex.obj N)).hom
  /-- Alpha commutes with coefficient extension and its canonical Hom comparison. -/
  alpha : ∀ (P A : Complex.{c, v, u} R),
    Da.extension.complex.map (D.alpha P A) ≫ Da.homComparison P ((tensor.{c, v, u} φ).obj A) ≫
        homMap.{c, v, u} (𝟙 (Da.extension.complex.obj P)) (Q.tensorComparison A) =
      Q.tensorComparison (homComplex (R := R) P A) ≫
        (tensor.{c, v, u} φ').map (Da.homComparison P A) ≫
        D'.alpha (Da.extension.complex.obj P) (Da.extension.complex.obj A)
  /-- Sigma commutes with coefficient extension for every compatible q', including
  arbitrary targets and compatible semilinear target maps, not only Eb(N). -/
  sigma : ∀ (P A : Complex.{c, v, u} R) (N : Complex.{c, v, u} S) (N' : Complex.{c, v, u} S')
    (q : D.extension.complex.obj A ⟶ N)
    (w : Db.extension.complex.obj N ⟶ N')
    (q' : D'.extension.complex.obj (Da.extension.complex.obj A) ⟶ N'),
    (Q.extensionIso.app A).hom ≫ q' = Db.extension.complex.map q ≫ w →
      Db.extension.complex.map (D.sigma P A N q) ≫
          Db.homComparison (D.extension.complex.obj P) N ≫
          homMap.{c, v, u} (Q.extensionIso.app P).inv w =
        (Q.extensionIso.app (homComplex (R := R) P A)).hom ≫
          D'.extension.complex.map (Da.homComparison P A) ≫
          D'.sigma (Da.extension.complex.obj P) (Da.extension.complex.obj A) N' q'

structure CoefficientExtensionAssociators
    (F : ∀ (R S : Sheaf J CommRingCat.{max c v u}) (φ : R ⟶ S),
      NormalizedCoefficientMaps.{c, v, u} φ) where
  /-- Extension along an identity ring map is canonically the identity. -/
  unit : ∀ (R : Sheaf J CommRingCat.{max c v u}),
    (F R R (𝟙 R)).extension.complex ≅ 𝟭 (Complex.{c, v, u} R)
  /-- Multiplication gives the forward unit formula. -/
  unit_pure : ∀ (R : Sheaf J CommRingCat.{max c v u})
    (X : Complex.{c, v, u} R) (n : ℤ) (V : Cᵒᵖ)
    (r : R.obj.obj V) (x : (X.X n).val.obj V),
    ((((unit R).app X).hom.f n).val.app V)
        ((F R R (𝟙 R)).extension.section X n V r x) = r • x
  /-- The inverse inserts the unit. -/
  unit_inv : ∀ (R : Sheaf J CommRingCat.{max c v u})
    (X : Complex.{c, v, u} R) (n : ℤ) (V : Cᵒᵖ) (x : (X.X n).val.obj V),
    ((((unit R).app X).inv.f n).val.app V) x =
      (F R R (𝟙 R)).extension.section X n V 1 x
  /-- Restriction along the identity is the identity functor. -/
  resUnit : ∀ (R : Sheaf J CommRingCat.{max c v u}),
    restriction.{c, v, u} (𝟙 R) ≅ 𝟭 (Complex.{c, v, u} R)
  /-- The restriction unit leaves every section unchanged. -/
  resUnit_pure : ∀ (R : Sheaf J CommRingCat.{max c v u})
    (X : Complex.{c, v, u} R) (n : ℤ) (V : Cᵒᵖ) (x : (X.X n).val.obj V),
    ((((resUnit R).app X).hom.f n).val.app V) x = x
  /-- The inverse restriction unit leaves every section unchanged. -/
  resUnit_inv : ∀ (R : Sheaf J CommRingCat.{max c v u})
    (X : Complex.{c, v, u} R) (n : ℤ) (V : Cᵒᵖ) (x : (X.X n).val.obj V),
    ((((resUnit R).app X).inv.f n).val.app V) x = x
  /-- The ordinary R-linear tensor unit identification. -/
  tensorUnit : ∀ (R : Sheaf J CommRingCat.{max c v u}),
    tensor.{c, v, u} (𝟙 R) ≅ 𝟭 (Complex.{c, v, u} R)
  /-- The tensor unit contracts r tensor x to rx. -/
  tensorUnit_pure : ∀ (R : Sheaf J CommRingCat.{max c v u})
    (X : Complex.{c, v, u} R) (n : ℤ) (V : Cᵒᵖ)
    (r : R.obj.obj V) (x : (X.X n).val.obj V),
    ((((tensorUnit R).app X).hom.f n).val.app V)
        (tensorSection.{c, v, u} (𝟙 R) X n V r x) = r • x
  /-- Its inverse inserts the unit of R. -/
  tensorUnit_inv : ∀ (R : Sheaf J CommRingCat.{max c v u})
    (X : Complex.{c, v, u} R) (n : ℤ) (V : Cᵒᵖ) (x : (X.X n).val.obj V),
    ((((tensorUnit R).app X).inv.f n).val.app V) x =
      tensorSection.{c, v, u} (𝟙 R) X n V 1 x
  /-- Contract two successive ordinary extensions. -/
  comp : ∀ (R S T : Sheaf J CommRingCat.{max c v u}) (φ : R ⟶ S) (ψ : S ⟶ T),
    (F R S φ).extension.complex ⋙ (F S T ψ).extension.complex ≅
      (F R T (φ ≫ ψ)).extension.complex
  /-- The contraction is multiplication of coefficients. -/
  comp_pure : ∀ (R S T : Sheaf J CommRingCat.{max c v u})
    (φ : R ⟶ S) (ψ : S ⟶ T) (X : Complex.{c, v, u} R)
    (n : ℤ) (V : Cᵒᵖ) (t : T.obj.obj V) (s : S.obj.obj V) (x : (X.X n).val.obj V),
    ((((comp R S T φ ψ).app X).hom.f n).val.app V)
        ((F S T ψ).extension.section ((F R S φ).extension.complex.obj X) n V t
          ((F R S φ).extension.section X n V s x)) =
      (F R T (φ ≫ ψ)).extension.section X n V (t * ψ.hom.app V s) x
  /-- The inverse contraction inserts a unit in the inner extension. -/
  comp_inv : ∀ (R S T : Sheaf J CommRingCat.{max c v u})
    (φ : R ⟶ S) (ψ : S ⟶ T) (X : Complex.{c, v, u} R)
    (n : ℤ) (V : Cᵒᵖ) (t : T.obj.obj V) (x : (X.X n).val.obj V),
    ((((comp R S T φ ψ).app X).inv.f n).val.app V)
        ((F R T (φ ≫ ψ)).extension.section X n V t x) =
      (F S T ψ).extension.section ((F R S φ).extension.complex.obj X) n V t
        ((F R S φ).extension.section X n V 1 x)
  /-- Restriction along a composite agrees with successive restriction. -/
  resComp : ∀ (R S T : Sheaf J CommRingCat.{max c v u}) (φ : R ⟶ S) (ψ : S ⟶ T),
    restriction.{c, v, u} ψ ⋙ restriction.{c, v, u} φ ≅ restriction.{c, v, u} (φ ≫ ψ)
  /-- This restriction identification is the identity on sections. -/
  resComp_pure : ∀ (R S T : Sheaf J CommRingCat.{max c v u})
    (φ : R ⟶ S) (ψ : S ⟶ T) (N : Complex.{c, v, u} T)
    (n : ℤ) (V : Cᵒᵖ) (x : (N.X n).val.obj V),
    ((((resComp R S T φ ψ).app N).hom.f n).val.app V) x = x
  /-- The inverse restriction identification is also the identity on sections. -/
  resComp_inv : ∀ (R S T : Sheaf J CommRingCat.{max c v u})
    (φ : R ⟶ S) (ψ : S ⟶ T) (N : Complex.{c, v, u} T)
    (n : ℤ) (V : Cᵒᵖ) (x : (N.X n).val.obj V),
    ((((resComp R S T φ ψ).app N).inv.f n).val.app V) x = x

structure CoefficientChainPasting
    {F : ∀ (R S : Sheaf J CommRingCat.{max c v u}) (φ : R ⟶ S),
      NormalizedCoefficientMaps.{c, v, u} φ}
    (L : CoefficientExtensionAssociators.{c, v, u} F)
    (Q : CoefficientChainSquares.{c, v, u} F) : Prop where
  /-- Kappa is the identity after the unit identifications. -/
  kappa_id : ∀ (R S : Sheaf J CommRingCat.{max c v u}) (φ : R ⟶ S)
    (h : φ ≫ 𝟙 S = 𝟙 R ≫ φ) (X : Complex.{c, v, u} R),
    ((Q.square R S R S φ (𝟙 R) (𝟙 S) φ h).extensionIso.app X).hom ≫
        (F R S φ).extension.complex.map (((L.unit R).app X).hom) =
      ((L.unit S).app ((F R S φ).extension.complex.obj X)).hom
  /-- Mu is the identity after the unit identifications. -/
  mu_id : ∀ (R S : Sheaf J CommRingCat.{max c v u}) (φ : R ⟶ S)
    (h : φ ≫ 𝟙 S = 𝟙 R ≫ φ) (N : Complex.{c, v, u} S),
    (Q.square R S R S φ (𝟙 R) (𝟙 S) φ h).restrictionMate.app N ≫
        (restriction.{c, v, u} φ).map (((L.unit S).app N).hom) =
      ((L.unit R).app ((restriction.{c, v, u} φ).obj N)).hom
  /-- Tau is the identity after the unit identifications. -/
  tau_id : ∀ (R S : Sheaf J CommRingCat.{max c v u}) (φ : R ⟶ S)
    (h : φ ≫ 𝟙 S = 𝟙 R ≫ φ) (X : Complex.{c, v, u} R),
    (Q.square R S R S φ (𝟙 R) (𝟙 S) φ h).tensorComparison X ≫
        (tensor.{c, v, u} φ).map (((L.unit R).app X).hom) =
      ((L.unit R).app ((tensor.{c, v, u} φ).obj X)).hom
  /-- Kappa for a pasted square is successive kappa, transported by associators. -/
  kappa_comp : ∀ (R S R' S' R'' S'' : Sheaf J CommRingCat.{max c v u})
    (φ : R ⟶ S) (a : R ⟶ R') (b : S ⟶ S') (φ' : R' ⟶ S')
    (c' : R' ⟶ R'') (d : S' ⟶ S'') (φ'' : R'' ⟶ S'')
    (h : φ ≫ b = a ≫ φ') (h' : φ' ≫ d = c' ≫ φ'')
    (hh : φ ≫ (b ≫ d) = (a ≫ c') ≫ φ'') (X : Complex.{c, v, u} R),
    (F S' S'' d).extension.complex.map
        (((Q.square R S R' S' φ a b φ' h).extensionIso.app X).hom) ≫
        ((Q.square R' S' R'' S'' φ' c' d φ'' h').extensionIso.app
          ((F R R' a).extension.complex.obj X)).hom =
      ((L.comp S S' S'' b d).app ((F R S φ).extension.complex.obj X)).hom ≫
        ((Q.square R S R'' S'' φ (a ≫ c') (b ≫ d) φ'' hh).extensionIso.app X).hom ≫
        (F R'' S'' φ'').extension.complex.map (((L.comp R R' R'' a c').app X).inv)
  /-- Mu for a pasted square is successive mu, with restriction of the associator. -/
  mu_comp : ∀ (R S R' S' R'' S'' : Sheaf J CommRingCat.{max c v u})
    (φ : R ⟶ S) (a : R ⟶ R') (b : S ⟶ S') (φ' : R' ⟶ S')
    (c' : R' ⟶ R'') (d : S' ⟶ S'') (φ'' : R'' ⟶ S'')
    (h : φ ≫ b = a ≫ φ') (h' : φ' ≫ d = c' ≫ φ'')
    (hh : φ ≫ (b ≫ d) = (a ≫ c') ≫ φ'') (N : Complex.{c, v, u} S),
    (F R' R'' c').extension.complex.map
        ((Q.square R S R' S' φ a b φ' h).restrictionMate.app N) ≫
        (Q.square R' S' R'' S'' φ' c' d φ'' h').restrictionMate.app
          ((F S S' b).extension.complex.obj N) =
      ((L.comp R R' R'' a c').app ((restriction.{c, v, u} φ).obj N)).hom ≫
        (Q.square R S R'' S'' φ (a ≫ c') (b ≫ d) φ'' hh).restrictionMate.app N ≫
        (restriction.{c, v, u} φ'').map (((L.comp S S' S'' b d).app N).inv)
  /-- Tau for a pasted square is successive tau, transported by associators. -/
  tau_comp : ∀ (R S R' S' R'' S'' : Sheaf J CommRingCat.{max c v u})
    (φ : R ⟶ S) (a : R ⟶ R') (b : S ⟶ S') (φ' : R' ⟶ S')
    (c' : R' ⟶ R'') (d : S' ⟶ S'') (φ'' : R'' ⟶ S'')
    (h : φ ≫ b = a ≫ φ') (h' : φ' ≫ d = c' ≫ φ'')
    (hh : φ ≫ (b ≫ d) = (a ≫ c') ≫ φ'') (X : Complex.{c, v, u} R),
    (F R' R'' c').extension.complex.map
        ((Q.square R S R' S' φ a b φ' h).tensorComparison X) ≫
        (Q.square R' S' R'' S'' φ' c' d φ'' h').tensorComparison
          ((F R R' a).extension.complex.obj X) =
      ((L.comp R R' R'' a c').app ((tensor.{c, v, u} φ).obj X)).hom ≫
        (Q.square R S R'' S'' φ (a ≫ c') (b ≫ d) φ'' hh).tensorComparison X ≫
        (tensor.{c, v, u} φ'').map (((L.comp R R' R'' a c').app X).inv)

structure CoefficientHomIteration
    {F : ∀ (R S : Sheaf J CommRingCat.{max c v u}) (φ : R ⟶ S),
      NormalizedCoefficientMaps.{c, v, u} φ}
    (L : CoefficientExtensionAssociators.{c, v, u} F) : Prop where
  /-- Both contractions of three scalar extensions agree. -/
  associativity : ∀ (R S T V : Sheaf J CommRingCat.{max c v u})
    (φ : R ⟶ S) (ψ : S ⟶ T) (ξ : T ⟶ V) (X : Complex.{c, v, u} R),
    (F T V ξ).extension.complex.map (((L.comp R S T φ ψ).app X).hom) ≫
        ((L.comp R T V (φ ≫ ψ) ξ).app X).hom =
      ((L.comp S T V ψ ξ).app ((F R S φ).extension.complex.obj X)).hom ≫
        ((L.comp R S V φ (ψ ≫ ξ)).app X).hom ≫
        eqToHom (congrArg
          (fun f : R ⟶ V ↦ (F R V f).extension.complex.obj X)
          (Category.assoc φ ψ ξ).symm)
  /-- Inserting an identity extension before extension gives the same contraction. -/
  left_unit : ∀ (R S : Sheaf J CommRingCat.{max c v u})
    (φ : R ⟶ S) (X : Complex.{c, v, u} R),
    ((L.comp R R S (𝟙 R) φ).app X).hom ≫
        eqToHom (congrArg (fun f : R ⟶ S ↦ (F R S f).extension.complex.obj X)
          (Category.id_comp φ)) =
      (F R S φ).extension.complex.map (((L.unit R).app X).hom)
  /-- Inserting an identity extension after extension gives the same contraction. -/
  right_unit : ∀ (R S : Sheaf J CommRingCat.{max c v u})
    (φ : R ⟶ S) (X : Complex.{c, v, u} R),
    ((L.comp R S S φ (𝟙 S)).app X).hom ≫
        eqToHom (congrArg (fun f : R ⟶ S ↦ (F R S f).extension.complex.obj X)
          (Category.comp_id φ)) =
      ((L.unit S).app ((F R S φ).extension.complex.obj X)).hom
  /-- Nu for identity coefficients becomes the identity tensor identification. -/
  nu_id : ∀ (R : Sheaf J CommRingCat.{max c v u}) (X : Complex.{c, v, u} R),
    ((F R R (𝟙 R)).chains.nu.app X).hom ≫
        (restriction.{c, v, u} (𝟙 R)).map (((L.unit R).app X).hom) ≫
        ((L.resUnit R).app X).hom =
      ((L.tensorUnit R).app X).hom
  /-- Chi for identity coefficients becomes the identity Hom comparison. -/
  chi_id : ∀ (R : Sheaf J CommRingCat.{max c v u}) (P A : Complex.{c, v, u} R),
    (F R R (𝟙 R)).homComparison P A ≫
        homMap.{c, v, u} (((L.unit R).app P).inv) (((L.unit R).app A).hom) =
      ((L.unit R).app (homComplex (R := R) P A)).hom
  /-- Theta for identity coefficients is the identity after unit identifications. -/
  theta_id : ∀ (R : Sheaf J CommRingCat.{max c v u}) (P N : Complex.{c, v, u} R),
    ((F R R (𝟙 R)).chains.theta P N).hom ≫
        homMap.{c, v, u} (𝟙 P) (((L.resUnit R).app N).hom) =
      ((L.resUnit R).app
        (homComplex (R := R) ((F R R (𝟙 R)).extension.complex.obj P) N)).hom ≫
        homMap.{c, v, u} (((L.unit R).app P).inv) (𝟙 N)
  /-- Alpha for identity coefficients is the identity after tensor unit contraction. -/
  alpha_id : ∀ (R : Sheaf J CommRingCat.{max c v u}) (P A : Complex.{c, v, u} R),
    (F R R (𝟙 R)).alpha P A ≫
        homMap.{c, v, u} (𝟙 P) (((L.tensorUnit R).app A).hom) =
      ((L.tensorUnit R).app (homComplex (R := R) P A)).hom
  /-- Sigma for identity coefficients is composition with its arbitrary target map. -/
  sigma_id : ∀ (R : Sheaf J CommRingCat.{max c v u}) (P A N : Complex.{c, v, u} R)
    (q : (F R R (𝟙 R)).extension.complex.obj A ⟶ N),
    (F R R (𝟙 R)).sigma P A N q ≫ homMap.{c, v, u} (((L.unit R).app P).inv) (𝟙 N) =
      ((L.unit R).app (homComplex (R := R) P A)).hom ≫
        homMap.{c, v, u} (𝟙 P) ((((L.unit R).app A).inv) ≫ q)
  /-- Nu respects contraction of an iterated scalar tensor. -/
  nu_comp : ∀ (R S T : Sheaf J CommRingCat.{max c v u})
    (φ : R ⟶ S) (ψ : S ⟶ T) (X : Complex.{c, v, u} R),
    L.underlyingComp φ ψ X ≫ (restriction.{c, v, u} φ).map
        (((F S T ψ).chains.nu.app ((F R S φ).extension.complex.obj X)).hom) =
      ((F R T (φ ≫ ψ)).chains.nu.app X).hom ≫
        ((L.resComp R S T φ ψ).app ((F R T (φ ≫ ψ)).extension.complex.obj X)).inv ≫
        (restriction.{c, v, u} φ).map
          ((restriction.{c, v, u} ψ).map (((L.comp R S T φ ψ).app X).inv))
  /-- Successive Hom comparisons contract to the direct Hom comparison. -/
  chi_comp : ∀ (R S T : Sheaf J CommRingCat.{max c v u})
    (φ : R ⟶ S) (ψ : S ⟶ T) (P A : Complex.{c, v, u} R),
    (F S T ψ).extension.complex.map ((F R S φ).homComparison P A) ≫
        (F S T ψ).homComparison ((F R S φ).extension.complex.obj P)
          ((F R S φ).extension.complex.obj A) ≫
        homMap.{c, v, u} (((L.comp R S T φ ψ).app P).inv)
          (((L.comp R S T φ ψ).app A).hom) =
      ((L.comp R S T φ ψ).app (homComplex (R := R) P A)).hom ≫
        (F R T (φ ≫ ψ)).homComparison P A
  /-- Successive adjunction maps evaluate at the same twice-inserted unit. -/
  theta_comp : ∀ (R S T : Sheaf J CommRingCat.{max c v u})
    (φ : R ⟶ S) (ψ : S ⟶ T) (P : Complex.{c, v, u} R) (N : Complex.{c, v, u} T),
    (restriction.{c, v, u} φ).map
        (((F S T ψ).chains.theta ((F R S φ).extension.complex.obj P) N).hom) ≫
        ((F R S φ).chains.theta P ((restriction.{c, v, u} ψ).obj N)).hom ≫
        homMap.{c, v, u} (𝟙 P) (((L.resComp R S T φ ψ).app N).hom) =
      ((L.resComp R S T φ ψ).app (homComplex (R := T)
        ((F S T ψ).extension.complex.obj ((F R S φ).extension.complex.obj P)) N)).hom ≫
        (restriction.{c, v, u} (φ ≫ ψ)).map
          (homMap.{c, v, u} (((L.comp R S T φ ψ).app P).inv) (𝟙 N)) ≫
        ((F R T (φ ≫ ψ)).chains.theta P N).hom
  /-- Alpha commutes with contraction of the iterated tensor and Hom evaluation. -/
  alpha_comp : ∀ (R S T : Sheaf J CommRingCat.{max c v u})
    (φ : R ⟶ S) (ψ : S ⟶ T) (P A : Complex.{c, v, u} R),
    (F R T (φ ≫ ψ)).alpha P A ≫
        homMap.{c, v, u} (𝟙 P) (L.underlyingComp φ ψ A) =
      L.underlyingComp φ ψ (homComplex (R := R) P A) ≫
        (restriction.{c, v, u} φ).map
          ((tensor.{c, v, u} ψ).map ((F R S φ).homComparison P A)) ≫
        (restriction.{c, v, u} φ).map
          ((F S T ψ).alpha ((F R S φ).extension.complex.obj P)
            ((F R S φ).extension.complex.obj A)) ≫
        ((F R S φ).chains.theta P
          ((tensor.{c, v, u} ψ).obj ((F R S φ).extension.complex.obj A))).hom
  /-- Successive sigma agrees for any target and any compatible chain map. -/
  sigma_comp : ∀ (R S T : Sheaf J CommRingCat.{max c v u})
    (φ : R ⟶ S) (ψ : S ⟶ T) (P A : Complex.{c, v, u} R)
    (N : Complex.{c, v, u} T)
    (q : (F S T ψ).extension.complex.obj ((F R S φ).extension.complex.obj A) ⟶ N),
    (F S T ψ).extension.complex.map ((F R S φ).homComparison P A) ≫
        (F S T ψ).sigma ((F R S φ).extension.complex.obj P)
          ((F R S φ).extension.complex.obj A) N q ≫
        homMap.{c, v, u} (((L.comp R S T φ ψ).app P).inv) (𝟙 N) =
      ((L.comp R S T φ ψ).app (homComplex (R := R) P A)).hom ≫
        (F R T (φ ≫ ψ)).sigma P A N ((((L.comp R S T φ ψ).app A).inv) ≫ q)
```

## New

The following are the repaired records, shared law definitions and derived
inverse theorems, verbatim (unchanged intervening declarations are included):

```lean
/-- The tensor coefficient map is the expected map on all local generators.
Source: Stacks 03CY, 03CZ and 0A8X; the corresponding node equation
(blueprint: lem-sfb-scalar-hom-chain-coefficient-coherence). -/
def NormalizedCoefficientCompatibility.tensor_pure_law
    {R S R' S' : Sheaf J CommRingCat.{max c v u}}
    {φ : R ⟶ S} {a : R ⟶ R'} {b : S ⟶ S'} {φ' : R' ⟶ S'}
    {D : NormalizedCoefficientMaps.{c, v, u} φ}
    {Da : NormalizedCoefficientMaps.{c, v, u} a}
    {Db : NormalizedCoefficientMaps.{c, v, u} b}
    {D' : NormalizedCoefficientMaps.{c, v, u} φ'}
    (Q : NormalizedCoefficientSquare.{c, v, u} D Da Db D') : Prop :=
  ∀ (A : Complex.{c, v, u} R) (n : ℤ) (V : Cᵒᵖ)
    (r : R'.obj.obj V) (s : S.obj.obj V) (x : (A.X n).val.obj V),
    (((Q.tensorComparison A).f n).val.app V)
        (Da.extension.section ((tensor.{c, v, u} φ).obj A) n V r
          (tensorSection.{c, v, u} φ A n V s x)) =
      tensorSection.{c, v, u} φ' (Da.extension.complex.obj A) n V
        (φ'.hom.app V r * b.hom.app V s) (Da.extension.section A n V 1 x)

/-- Nu commutes with the canonical coefficient maps.
Source: Stacks 03CY, 03CZ and 0A8X; the corresponding node equation
(blueprint: lem-sfb-scalar-hom-chain-coefficient-coherence). -/
def NormalizedCoefficientCompatibility.nu_law
    {R S R' S' : Sheaf J CommRingCat.{max c v u}}
    {φ : R ⟶ S} {a : R ⟶ R'} {b : S ⟶ S'} {φ' : R' ⟶ S'}
    {D : NormalizedCoefficientMaps.{c, v, u} φ}
    {Da : NormalizedCoefficientMaps.{c, v, u} a}
    {Db : NormalizedCoefficientMaps.{c, v, u} b}
    {D' : NormalizedCoefficientMaps.{c, v, u} φ'}
    (Q : NormalizedCoefficientSquare.{c, v, u} D Da Db D') : Prop :=
  ∀ (A : Complex.{c, v, u} R),
    Q.tensorComparison A ≫ (D'.chains.nu.app (Da.extension.complex.obj A)).hom =
      Da.extension.complex.map (D.chains.nu.app A).hom ≫
        Q.restrictionMate.app (D.extension.complex.obj A) ≫
        (restriction.{c, v, u} φ').map (Q.extensionIso.app A).hom

/-- Theta commutes with the canonical Hom comparisons and the restriction mate.
Source: Stacks 03CY, 03CZ and 0A8X; the corresponding node equation
(blueprint: lem-sfb-scalar-hom-chain-coefficient-coherence). -/
def NormalizedCoefficientCompatibility.theta_law
    {R S R' S' : Sheaf J CommRingCat.{max c v u}}
    {φ : R ⟶ S} {a : R ⟶ R'} {b : S ⟶ S'} {φ' : R' ⟶ S'}
    {D : NormalizedCoefficientMaps.{c, v, u} φ}
    {Da : NormalizedCoefficientMaps.{c, v, u} a}
    {Db : NormalizedCoefficientMaps.{c, v, u} b}
    {D' : NormalizedCoefficientMaps.{c, v, u} φ'}
    (Q : NormalizedCoefficientSquare.{c, v, u} D Da Db D') : Prop :=
  ∀ (P : Complex.{c, v, u} R) (N : Complex.{c, v, u} S),
    Da.extension.complex.map (D.chains.theta P N).hom ≫
        Da.homComparison P ((restriction.{c, v, u} φ).obj N) ≫
        homMap.{c, v, u} (𝟙 (Da.extension.complex.obj P)) (Q.restrictionMate.app N) =
      Q.restrictionMate.app (homComplex (R := S) (D.extension.complex.obj P) N) ≫
        (restriction.{c, v, u} φ').map (Db.homComparison (D.extension.complex.obj P) N) ≫
        (restriction.{c, v, u} φ').map (homMap.{c, v, u} (Q.extensionIso.app P).inv
          (𝟙 (Db.extension.complex.obj N))) ≫
        (D'.chains.theta (Da.extension.complex.obj P) (Db.extension.complex.obj N)).hom

/-- Alpha commutes with coefficient extension and its canonical Hom comparison.
Source: Stacks 03CY, 03CZ and 0A8X; the corresponding node equation
(blueprint: lem-sfb-scalar-hom-chain-coefficient-coherence). -/
def NormalizedCoefficientCompatibility.alpha_law
    {R S R' S' : Sheaf J CommRingCat.{max c v u}}
    {φ : R ⟶ S} {a : R ⟶ R'} {b : S ⟶ S'} {φ' : R' ⟶ S'}
    {D : NormalizedCoefficientMaps.{c, v, u} φ}
    {Da : NormalizedCoefficientMaps.{c, v, u} a}
    {Db : NormalizedCoefficientMaps.{c, v, u} b}
    {D' : NormalizedCoefficientMaps.{c, v, u} φ'}
    (Q : NormalizedCoefficientSquare.{c, v, u} D Da Db D') : Prop :=
  ∀ (P A : Complex.{c, v, u} R),
    Da.extension.complex.map (D.alpha P A) ≫ Da.homComparison P ((tensor.{c, v, u} φ).obj A) ≫
        homMap.{c, v, u} (𝟙 (Da.extension.complex.obj P)) (Q.tensorComparison A) =
      Q.tensorComparison (homComplex (R := R) P A) ≫
        (tensor.{c, v, u} φ').map (Da.homComparison P A) ≫
        D'.alpha (Da.extension.complex.obj P) (Da.extension.complex.obj A)

/-- Sigma commutes with coefficient extension for every compatible q', including
  arbitrary targets and compatible semilinear target maps, not only Eb(N).
Source: Stacks 03CY, 03CZ and 0A8X; the corresponding node equation
(blueprint: lem-sfb-scalar-hom-chain-coefficient-coherence). -/
def NormalizedCoefficientCompatibility.sigma_law
    {R S R' S' : Sheaf J CommRingCat.{max c v u}}
    {φ : R ⟶ S} {a : R ⟶ R'} {b : S ⟶ S'} {φ' : R' ⟶ S'}
    {D : NormalizedCoefficientMaps.{c, v, u} φ}
    {Da : NormalizedCoefficientMaps.{c, v, u} a}
    {Db : NormalizedCoefficientMaps.{c, v, u} b}
    {D' : NormalizedCoefficientMaps.{c, v, u} φ'}
    (Q : NormalizedCoefficientSquare.{c, v, u} D Da Db D') : Prop :=
  ∀ (P A : Complex.{c, v, u} R) (N : Complex.{c, v, u} S) (N' : Complex.{c, v, u} S')
    (q : D.extension.complex.obj A ⟶ N)
    (w : Db.extension.complex.obj N ⟶ N')
    (q' : D'.extension.complex.obj (Da.extension.complex.obj A) ⟶ N'),
    (Q.extensionIso.app A).hom ≫ q' = Db.extension.complex.map q ≫ w →
      Db.extension.complex.map (D.sigma P A N q) ≫
          Db.homComparison (D.extension.complex.obj P) N ≫
          homMap.{c, v, u} (Q.extensionIso.app P).inv w =
        (Q.extensionIso.app (homComplex (R := R) P A)).hom ≫
          D'.extension.complex.map (Da.homComparison P A) ≫
          D'.sigma (Da.extension.complex.obj P) (Da.extension.complex.obj A) N' q'

/-- Coefficient compatibility of all four normalized chain maps. These are equations
of actual chain maps for a general commuting square, without a flatness assumption.
Source: Stacks 03CZ and 0A8X, the DAG's generator calculation
(blueprint: lem-sfb-scalar-hom-chain-coefficient-coherence). -/
structure NormalizedCoefficientCompatibility
    {R S R' S' : Sheaf J CommRingCat.{max c v u}}
    {φ : R ⟶ S} {a : R ⟶ R'} {b : S ⟶ S'} {φ' : R' ⟶ S'}
    {D : NormalizedCoefficientMaps.{c, v, u} φ}
    {Da : NormalizedCoefficientMaps.{c, v, u} a}
    {Db : NormalizedCoefficientMaps.{c, v, u} b}
    {D' : NormalizedCoefficientMaps.{c, v, u} φ'}
    (Q : NormalizedCoefficientSquare.{c, v, u} D Da Db D') : Prop where
  /-- The tensor coefficient map is the expected map on all local generators. -/
  tensor_pure : NormalizedCoefficientCompatibility.tensor_pure_law Q
  /-- Nu commutes with the canonical coefficient maps. -/
  nu : NormalizedCoefficientCompatibility.nu_law Q
  /-- Theta commutes with the canonical Hom comparisons and the restriction mate. -/
  theta : NormalizedCoefficientCompatibility.theta_law Q
  /-- Alpha commutes with coefficient extension and its canonical Hom comparison. -/
  alpha : NormalizedCoefficientCompatibility.alpha_law Q
  /-- Sigma commutes with coefficient extension for every compatible q', including
  arbitrary targets and compatible semilinear target maps, not only Eb(N). -/
  sigma : NormalizedCoefficientCompatibility.sigma_law Q

/-- Naturality of the tensor comparison defined through nu, kappa and mu.
Source: Stacks 03CY and 03CZ
(blueprint: lem-sfb-scalar-hom-chain-coefficient-coherence). -/
def NormalizedCoefficientSquare.TensorNatural
    {R S R' S' : Sheaf J CommRingCat.{max c v u}}
    {φ : R ⟶ S} {a : R ⟶ R'} {b : S ⟶ S'} {φ' : R' ⟶ S'}
    {D : NormalizedCoefficientMaps.{c, v, u} φ}
    {Da : NormalizedCoefficientMaps.{c, v, u} a}
    {Db : NormalizedCoefficientMaps.{c, v, u} b}
    {D' : NormalizedCoefficientMaps.{c, v, u} φ'}
    (Q : NormalizedCoefficientSquare.{c, v, u} D Da Db D') : Prop :=
  ∀ (X Y : Complex.{c, v, u} R) (f : X ⟶ Y),
    Da.extension.complex.map ((tensor.{c, v, u} φ).map f) ≫ Q.tensorComparison Y =
      Q.tensorComparison X ≫ (tensor.{c, v, u} φ').map (Da.extension.complex.map f)

/-- A family of normalized iterated-extension associators and unit identifications.
Source: Stacks 03CY and 03CZ, node proof step 8
(blueprint: lem-sfb-scalar-hom-chain-coefficient-coherence). -/
structure CoefficientExtensionAssociators
    (F : ∀ (R S : Sheaf J CommRingCat.{max c v u}) (φ : R ⟶ S),
      NormalizedCoefficientMaps.{c, v, u} φ) where
  /-- Extension along an identity ring map is canonically the identity. -/
  unit : ∀ (R : Sheaf J CommRingCat.{max c v u}),
    (F R R (𝟙 R)).extension.complex ≅ 𝟭 (Complex.{c, v, u} R)
  /-- Multiplication gives the forward unit formula. -/
  unit_pure : ∀ (R : Sheaf J CommRingCat.{max c v u})
    (X : Complex.{c, v, u} R) (n : ℤ) (V : Cᵒᵖ)
    (r : R.obj.obj V) (x : (X.X n).val.obj V),
    ((((unit R).app X).hom.f n).val.app V)
        ((F R R (𝟙 R)).extension.section X n V r x) = r • x
  /-- Restriction along the identity is the identity functor. -/
  resUnit : ∀ (R : Sheaf J CommRingCat.{max c v u}),
    restriction.{c, v, u} (𝟙 R) ≅ 𝟭 (Complex.{c, v, u} R)
  /-- The restriction unit leaves every section unchanged. -/
  resUnit_pure : ∀ (R : Sheaf J CommRingCat.{max c v u})
    (X : Complex.{c, v, u} R) (n : ℤ) (V : Cᵒᵖ) (x : (X.X n).val.obj V),
    ((((resUnit R).app X).hom.f n).val.app V) x = x
  /-- The ordinary R-linear tensor unit identification. -/
  tensorUnit : ∀ (R : Sheaf J CommRingCat.{max c v u}),
    tensor.{c, v, u} (𝟙 R) ≅ 𝟭 (Complex.{c, v, u} R)
  /-- The tensor unit contracts r tensor x to rx. -/
  tensorUnit_pure : ∀ (R : Sheaf J CommRingCat.{max c v u})
    (X : Complex.{c, v, u} R) (n : ℤ) (V : Cᵒᵖ)
    (r : R.obj.obj V) (x : (X.X n).val.obj V),
    ((((tensorUnit R).app X).hom.f n).val.app V)
        (tensorSection.{c, v, u} (𝟙 R) X n V r x) = r • x
  /-- Contract two successive ordinary extensions. -/
  comp : ∀ (R S T : Sheaf J CommRingCat.{max c v u}) (φ : R ⟶ S) (ψ : S ⟶ T),
    (F R S φ).extension.complex ⋙ (F S T ψ).extension.complex ≅
      (F R T (φ ≫ ψ)).extension.complex
  /-- The contraction is multiplication of coefficients. -/
  comp_pure : ∀ (R S T : Sheaf J CommRingCat.{max c v u})
    (φ : R ⟶ S) (ψ : S ⟶ T) (X : Complex.{c, v, u} R)
    (n : ℤ) (V : Cᵒᵖ) (t : T.obj.obj V) (s : S.obj.obj V) (x : (X.X n).val.obj V),
    ((((comp R S T φ ψ).app X).hom.f n).val.app V)
        ((F S T ψ).extension.section ((F R S φ).extension.complex.obj X) n V t
          ((F R S φ).extension.section X n V s x)) =
      (F R T (φ ≫ ψ)).extension.section X n V (t * ψ.hom.app V s) x
  /-- Restriction along a composite agrees with successive restriction. -/
  resComp : ∀ (R S T : Sheaf J CommRingCat.{max c v u}) (φ : R ⟶ S) (ψ : S ⟶ T),
    restriction.{c, v, u} ψ ⋙ restriction.{c, v, u} φ ≅ restriction.{c, v, u} (φ ≫ ψ)
  /-- This restriction identification is the identity on sections. -/
  resComp_pure : ∀ (R S T : Sheaf J CommRingCat.{max c v u})
    (φ : R ⟶ S) (ψ : S ⟶ T) (N : Complex.{c, v, u} T)
    (n : ℤ) (V : Cᵒᵖ) (x : (N.X n).val.obj V),
    ((((resComp R S T φ ψ).app N).hom.f n).val.app V) x = x

/-- The inverse formula follows from the forward normalization and the isomorphism identities.
Source: Stacks 03CY, 03CZ; node proof step 8
(blueprint: lem-sfb-scalar-hom-chain-coefficient-coherence). -/
theorem CoefficientExtensionAssociators.unit_inv
    {F : ∀ (R S : Sheaf J CommRingCat.{max c v u}) (φ : R ⟶ S),
      NormalizedCoefficientMaps.{c, v, u} φ}
    (L : CoefficientExtensionAssociators.{c, v, u} F)
    (R : Sheaf J CommRingCat.{max c v u})
    (X : Complex.{c, v, u} R) (n : ℤ) (V : Cᵒᵖ) (x : (X.X n).val.obj V) :
    ((((L.unit R).app X).inv.f n).val.app V) x =
      (F R R (𝟙 R)).extension.section X n V 1 x := by
  have hf := L.unit_pure R X n V 1 x
  simp only [one_smul] at hf
  have hi := congrArg (fun z ↦ (((L.unit R).app X).inv.f n).val.app V z) hf
  have hh := congrArg (fun f ↦ (f.f n).val.app V ((F R R (𝟙 R)).extension.section X n V 1 x))
    ((L.unit R).app X).hom_inv_id
  exact hi.symm.trans hh

/-- The inverse formula follows from the forward normalization and the isomorphism identities.
Source: Stacks 03CY, 03CZ; node proof step 8
(blueprint: lem-sfb-scalar-hom-chain-coefficient-coherence). -/
theorem CoefficientExtensionAssociators.resUnit_inv
    {F : ∀ (R S : Sheaf J CommRingCat.{max c v u}) (φ : R ⟶ S),
      NormalizedCoefficientMaps.{c, v, u} φ}
    (L : CoefficientExtensionAssociators.{c, v, u} F)
    (R : Sheaf J CommRingCat.{max c v u})
    (X : Complex.{c, v, u} R) (n : ℤ) (V : Cᵒᵖ) (x : (X.X n).val.obj V) :
    ((((L.resUnit R).app X).inv.f n).val.app V) x = x := by
  have hf := L.resUnit_pure R X n V x
  have hi := congrArg (fun z ↦ (((L.resUnit R).app X).inv.f n).val.app V z) hf
  have hh := congrArg (fun f ↦ (f.f n).val.app V (x))
    ((L.resUnit R).app X).hom_inv_id
  exact hi.symm.trans hh

/-- The inverse formula follows from the forward normalization and the isomorphism identities.
Source: Stacks 03CY, 03CZ; node proof step 8
(blueprint: lem-sfb-scalar-hom-chain-coefficient-coherence). -/
theorem CoefficientExtensionAssociators.tensorUnit_inv
    {F : ∀ (R S : Sheaf J CommRingCat.{max c v u}) (φ : R ⟶ S),
      NormalizedCoefficientMaps.{c, v, u} φ}
    (L : CoefficientExtensionAssociators.{c, v, u} F)
    (R : Sheaf J CommRingCat.{max c v u})
    (X : Complex.{c, v, u} R) (n : ℤ) (V : Cᵒᵖ) (x : (X.X n).val.obj V) :
    ((((L.tensorUnit R).app X).inv.f n).val.app V) x =
      tensorSection.{c, v, u} (𝟙 R) X n V 1 x := by
  have hf := L.tensorUnit_pure R X n V 1 x
  simp only [one_smul] at hf
  have hi := congrArg (fun z ↦ (((L.tensorUnit R).app X).inv.f n).val.app V z) hf
  have hh := congrArg (fun f ↦ (f.f n).val.app V (tensorSection.{c, v, u} (𝟙 R) X n V 1 x))
    ((L.tensorUnit R).app X).hom_inv_id
  exact hi.symm.trans hh

/-- The inverse formula follows from the forward normalization and the isomorphism identities.
Source: Stacks 03CY, 03CZ; node proof step 8
(blueprint: lem-sfb-scalar-hom-chain-coefficient-coherence). -/
theorem CoefficientExtensionAssociators.comp_inv
    {F : ∀ (R S : Sheaf J CommRingCat.{max c v u}) (φ : R ⟶ S),
      NormalizedCoefficientMaps.{c, v, u} φ}
    (L : CoefficientExtensionAssociators.{c, v, u} F)
    (R S T : Sheaf J CommRingCat.{max c v u})
    (φ : R ⟶ S) (ψ : S ⟶ T) (X : Complex.{c, v, u} R)
    (n : ℤ) (V : Cᵒᵖ) (t : T.obj.obj V) (x : (X.X n).val.obj V) :
    ((((L.comp R S T φ ψ).app X).inv.f n).val.app V)
        ((F R T (φ ≫ ψ)).extension.section X n V t x) =
      (F S T ψ).extension.section ((F R S φ).extension.complex.obj X) n V t
        ((F R S φ).extension.section X n V 1 x) := by
  have hf := L.comp_pure R S T φ ψ X n V t 1 x
  simp only [map_one, mul_one] at hf
  have hi := congrArg (fun z ↦ (((L.comp R S T φ ψ).app X).inv.f n).val.app V z) hf
  have hh := congrArg (fun f ↦ (f.f n).val.app V
    ((F S T ψ).extension.section ((F R S φ).extension.complex.obj X) n V t
      ((F R S φ).extension.section X n V 1 x)))
    ((L.comp R S T φ ψ).app X).hom_inv_id
  exact hi.symm.trans hh

/-- The inverse formula follows from the forward normalization and the isomorphism identities.
Source: Stacks 03CY, 03CZ; node proof step 8
(blueprint: lem-sfb-scalar-hom-chain-coefficient-coherence). -/
theorem CoefficientExtensionAssociators.resComp_inv
    {F : ∀ (R S : Sheaf J CommRingCat.{max c v u}) (φ : R ⟶ S),
      NormalizedCoefficientMaps.{c, v, u} φ}
    (L : CoefficientExtensionAssociators.{c, v, u} F)
    (R S T : Sheaf J CommRingCat.{max c v u})
    (φ : R ⟶ S) (ψ : S ⟶ T) (N : Complex.{c, v, u} T)
    (n : ℤ) (V : Cᵒᵖ) (x : (N.X n).val.obj V) :
    ((((L.resComp R S T φ ψ).app N).inv.f n).val.app V) x = x := by
  have hf := L.resComp_pure R S T φ ψ N n V x
  have hi := congrArg (fun z ↦ (((L.resComp R S T φ ψ).app N).inv.f n).val.app V z) hf
  have hh := congrArg (fun f ↦ (f.f n).val.app V (x))
    ((L.resComp R S T φ ψ).app N).hom_inv_id
  exact hi.symm.trans hh

/-- The four coefficient equations for every square, with normalized natural comparisons.
Source: Stacks 03CY, 03CZ and 0A8X, node proof steps 1--7
(blueprint: lem-sfb-scalar-hom-chain-coefficient-coherence). -/
structure CoefficientChainSquares
    (F : ∀ (R S : Sheaf J CommRingCat.{max c v u}) (φ : R ⟶ S),
      NormalizedCoefficientMaps.{c, v, u} φ) where
  /-- Kappa and mu on each commuting coefficient square. -/
  square : ∀ (R S R' S' : Sheaf J CommRingCat.{max c v u})
    (φ : R ⟶ S) (a : R ⟶ R') (b : S ⟶ S') (φ' : R' ⟶ S'),
    φ ≫ b = a ≫ φ' →
      NormalizedCoefficientSquare.{c, v, u} (F R S φ) (F R R' a) (F S S' b) (F R' S' φ')
  /-- All four chain equations; sigma includes every compatible target w. -/
  compatible : ∀ (R S R' S' : Sheaf J CommRingCat.{max c v u})
    (φ : R ⟶ S) (a : R ⟶ R') (b : S ⟶ S') (φ' : R' ⟶ S')
    (h : φ ≫ b = a ≫ φ'),
    NormalizedCoefficientCompatibility.{c, v, u} (square R S R' S' φ a b φ' h)
  /-- The underlying tensor comparison is natural as a chain map. -/
  tensor_natural : ∀ (R S R' S' : Sheaf J CommRingCat.{max c v u})
    (φ : R ⟶ S) (a : R ⟶ R') (b : S ⟶ S') (φ' : R' ⟶ S')
    (h : φ ≫ b = a ≫ φ'),
    (square R S R' S' φ a b φ' h).TensorNatural

/-- Kappa is the identity after the unit identifications.
Source: Stacks 03CY, 03CZ and 0A8X; the corresponding node equation
(blueprint: lem-sfb-scalar-hom-chain-coefficient-coherence). -/
def CoefficientChainPasting.kappa_id_law
    {F : ∀ (R S : Sheaf J CommRingCat.{max c v u}) (φ : R ⟶ S),
      NormalizedCoefficientMaps.{c, v, u} φ}
    (L : CoefficientExtensionAssociators.{c, v, u} F)
    (Q : CoefficientChainSquares.{c, v, u} F) : Prop :=
  ∀ (R S : Sheaf J CommRingCat.{max c v u}) (φ : R ⟶ S)
    (h : φ ≫ 𝟙 S = 𝟙 R ≫ φ) (X : Complex.{c, v, u} R),
    ((Q.square R S R S φ (𝟙 R) (𝟙 S) φ h).extensionIso.app X).hom ≫
        (F R S φ).extension.complex.map (((L.unit R).app X).hom) =
      ((L.unit S).app ((F R S φ).extension.complex.obj X)).hom

/-- Mu is the identity after the unit identifications.
Source: Stacks 03CY, 03CZ and 0A8X; the corresponding node equation
(blueprint: lem-sfb-scalar-hom-chain-coefficient-coherence). -/
def CoefficientChainPasting.mu_id_law
    {F : ∀ (R S : Sheaf J CommRingCat.{max c v u}) (φ : R ⟶ S),
      NormalizedCoefficientMaps.{c, v, u} φ}
    (L : CoefficientExtensionAssociators.{c, v, u} F)
    (Q : CoefficientChainSquares.{c, v, u} F) : Prop :=
  ∀ (R S : Sheaf J CommRingCat.{max c v u}) (φ : R ⟶ S)
    (h : φ ≫ 𝟙 S = 𝟙 R ≫ φ) (N : Complex.{c, v, u} S),
    (Q.square R S R S φ (𝟙 R) (𝟙 S) φ h).restrictionMate.app N ≫
        (restriction.{c, v, u} φ).map (((L.unit S).app N).hom) =
      ((L.unit R).app ((restriction.{c, v, u} φ).obj N)).hom

/-- Tau is the identity after the unit identifications.
Source: Stacks 03CY, 03CZ and 0A8X; the corresponding node equation
(blueprint: lem-sfb-scalar-hom-chain-coefficient-coherence). -/
def CoefficientChainPasting.tau_id_law
    {F : ∀ (R S : Sheaf J CommRingCat.{max c v u}) (φ : R ⟶ S),
      NormalizedCoefficientMaps.{c, v, u} φ}
    (L : CoefficientExtensionAssociators.{c, v, u} F)
    (Q : CoefficientChainSquares.{c, v, u} F) : Prop :=
  ∀ (R S : Sheaf J CommRingCat.{max c v u}) (φ : R ⟶ S)
    (h : φ ≫ 𝟙 S = 𝟙 R ≫ φ) (X : Complex.{c, v, u} R),
    (Q.square R S R S φ (𝟙 R) (𝟙 S) φ h).tensorComparison X ≫
        (tensor.{c, v, u} φ).map (((L.unit R).app X).hom) =
      ((L.unit R).app ((tensor.{c, v, u} φ).obj X)).hom

/-- Kappa for a pasted square is successive kappa, transported by associators.
Source: Stacks 03CY, 03CZ and 0A8X; the corresponding node equation
(blueprint: lem-sfb-scalar-hom-chain-coefficient-coherence). -/
def CoefficientChainPasting.kappa_comp_law
    {F : ∀ (R S : Sheaf J CommRingCat.{max c v u}) (φ : R ⟶ S),
      NormalizedCoefficientMaps.{c, v, u} φ}
    (L : CoefficientExtensionAssociators.{c, v, u} F)
    (Q : CoefficientChainSquares.{c, v, u} F) : Prop :=
  ∀ (R S R' S' R'' S'' : Sheaf J CommRingCat.{max c v u})
    (φ : R ⟶ S) (a : R ⟶ R') (b : S ⟶ S') (φ' : R' ⟶ S')
    (c' : R' ⟶ R'') (d : S' ⟶ S'') (φ'' : R'' ⟶ S'')
    (h : φ ≫ b = a ≫ φ') (h' : φ' ≫ d = c' ≫ φ'')
    (hh : φ ≫ (b ≫ d) = (a ≫ c') ≫ φ'') (X : Complex.{c, v, u} R),
    (F S' S'' d).extension.complex.map
        (((Q.square R S R' S' φ a b φ' h).extensionIso.app X).hom) ≫
        ((Q.square R' S' R'' S'' φ' c' d φ'' h').extensionIso.app
          ((F R R' a).extension.complex.obj X)).hom =
      ((L.comp S S' S'' b d).app ((F R S φ).extension.complex.obj X)).hom ≫
        ((Q.square R S R'' S'' φ (a ≫ c') (b ≫ d) φ'' hh).extensionIso.app X).hom ≫
        (F R'' S'' φ'').extension.complex.map (((L.comp R R' R'' a c').app X).inv)

/-- Mu for a pasted square is successive mu, with restriction of the associator.
Source: Stacks 03CY, 03CZ and 0A8X; the corresponding node equation
(blueprint: lem-sfb-scalar-hom-chain-coefficient-coherence). -/
def CoefficientChainPasting.mu_comp_law
    {F : ∀ (R S : Sheaf J CommRingCat.{max c v u}) (φ : R ⟶ S),
      NormalizedCoefficientMaps.{c, v, u} φ}
    (L : CoefficientExtensionAssociators.{c, v, u} F)
    (Q : CoefficientChainSquares.{c, v, u} F) : Prop :=
  ∀ (R S R' S' R'' S'' : Sheaf J CommRingCat.{max c v u})
    (φ : R ⟶ S) (a : R ⟶ R') (b : S ⟶ S') (φ' : R' ⟶ S')
    (c' : R' ⟶ R'') (d : S' ⟶ S'') (φ'' : R'' ⟶ S'')
    (h : φ ≫ b = a ≫ φ') (h' : φ' ≫ d = c' ≫ φ'')
    (hh : φ ≫ (b ≫ d) = (a ≫ c') ≫ φ'') (N : Complex.{c, v, u} S),
    (F R' R'' c').extension.complex.map
        ((Q.square R S R' S' φ a b φ' h).restrictionMate.app N) ≫
        (Q.square R' S' R'' S'' φ' c' d φ'' h').restrictionMate.app
          ((F S S' b).extension.complex.obj N) =
      ((L.comp R R' R'' a c').app ((restriction.{c, v, u} φ).obj N)).hom ≫
        (Q.square R S R'' S'' φ (a ≫ c') (b ≫ d) φ'' hh).restrictionMate.app N ≫
        (restriction.{c, v, u} φ'').map (((L.comp S S' S'' b d).app N).inv)

/-- Tau for a pasted square is successive tau, transported by associators.
Source: Stacks 03CY, 03CZ and 0A8X; the corresponding node equation
(blueprint: lem-sfb-scalar-hom-chain-coefficient-coherence). -/
def CoefficientChainPasting.tau_comp_law
    {F : ∀ (R S : Sheaf J CommRingCat.{max c v u}) (φ : R ⟶ S),
      NormalizedCoefficientMaps.{c, v, u} φ}
    (L : CoefficientExtensionAssociators.{c, v, u} F)
    (Q : CoefficientChainSquares.{c, v, u} F) : Prop :=
  ∀ (R S R' S' R'' S'' : Sheaf J CommRingCat.{max c v u})
    (φ : R ⟶ S) (a : R ⟶ R') (b : S ⟶ S') (φ' : R' ⟶ S')
    (c' : R' ⟶ R'') (d : S' ⟶ S'') (φ'' : R'' ⟶ S'')
    (h : φ ≫ b = a ≫ φ') (h' : φ' ≫ d = c' ≫ φ'')
    (hh : φ ≫ (b ≫ d) = (a ≫ c') ≫ φ'') (X : Complex.{c, v, u} R),
    (F R' R'' c').extension.complex.map
        ((Q.square R S R' S' φ a b φ' h).tensorComparison X) ≫
        (Q.square R' S' R'' S'' φ' c' d φ'' h').tensorComparison
          ((F R R' a).extension.complex.obj X) =
      ((L.comp R R' R'' a c').app ((tensor.{c, v, u} φ).obj X)).hom ≫
        (Q.square R S R'' S'' φ (a ≫ c') (b ≫ d) φ'' hh).tensorComparison X ≫
        (tensor.{c, v, u} φ'').map (((L.comp R R' R'' a c').app X).inv)

/-- Identity coefficient squares and pasted coefficient squares give the same maps.
Source: Stacks 03CY, 03CZ and 0A8X, node proof steps 8--11
(blueprint: lem-sfb-scalar-hom-chain-coefficient-coherence). -/
structure CoefficientChainPasting
    {F : ∀ (R S : Sheaf J CommRingCat.{max c v u}) (φ : R ⟶ S),
      NormalizedCoefficientMaps.{c, v, u} φ}
    (L : CoefficientExtensionAssociators.{c, v, u} F)
    (Q : CoefficientChainSquares.{c, v, u} F) : Prop where
  /-- Kappa is the identity after the unit identifications. -/
  kappa_id : CoefficientChainPasting.kappa_id_law L Q
  /-- Mu is the identity after the unit identifications. -/
  mu_id : CoefficientChainPasting.mu_id_law L Q
  /-- Tau is the identity after the unit identifications. -/
  tau_id : CoefficientChainPasting.tau_id_law L Q
  /-- Kappa for a pasted square is successive kappa, transported by associators. -/
  kappa_comp : CoefficientChainPasting.kappa_comp_law L Q
  /-- Mu for a pasted square is successive mu, with restriction of the associator. -/
  mu_comp : CoefficientChainPasting.mu_comp_law L Q
  /-- Tau for a pasted square is successive tau, transported by associators. -/
  tau_comp : CoefficientChainPasting.tau_comp_law L Q

/-- The underlying R-linear identification for an iterated scalar tensor.
Source: Stacks 03CY and 03CZ, node proof steps 8 and 10
(blueprint: lem-sfb-scalar-hom-chain-coefficient-coherence). -/
def CoefficientExtensionAssociators.underlyingComp
    {F : ∀ (R S : Sheaf J CommRingCat.{max c v u}) (φ : R ⟶ S),
      NormalizedCoefficientMaps.{c, v, u} φ}
    (L : CoefficientExtensionAssociators.{c, v, u} F)
    {R S T : Sheaf J CommRingCat.{max c v u}} (φ : R ⟶ S) (ψ : S ⟶ T)
    (X : Complex.{c, v, u} R) :
    (tensor.{c, v, u} (φ ≫ ψ)).obj X ⟶
      (restriction.{c, v, u} φ).obj
        ((tensor.{c, v, u} ψ).obj ((F R S φ).extension.complex.obj X)) :=
  ((F R T (φ ≫ ψ)).chains.nu.app X).hom ≫
    ((L.resComp R S T φ ψ).app ((F R T (φ ≫ ψ)).extension.complex.obj X)).inv ≫
    (restriction.{c, v, u} φ).map
      ((restriction.{c, v, u} ψ).map (((L.comp R S T φ ψ).app X).inv)) ≫
    (restriction.{c, v, u} φ).map
      (((F S T ψ).chains.nu.app ((F R S φ).extension.complex.obj X)).inv)

attribute [local irreducible] CoefficientExtensionAssociators.underlyingComp

/-- Both contractions of three scalar extensions agree.
Source: Stacks 03CY, 03CZ and 0A8X; the corresponding node equation
(blueprint: lem-sfb-scalar-hom-chain-coefficient-coherence). -/
def CoefficientHomIteration.associativity_law
    {F : ∀ (R S : Sheaf J CommRingCat.{max c v u}) (φ : R ⟶ S),
      NormalizedCoefficientMaps.{c, v, u} φ}
    (L : CoefficientExtensionAssociators.{c, v, u} F) : Prop :=
  ∀ (R S T V : Sheaf J CommRingCat.{max c v u})
    (φ : R ⟶ S) (ψ : S ⟶ T) (ξ : T ⟶ V) (X : Complex.{c, v, u} R),
    (F T V ξ).extension.complex.map (((L.comp R S T φ ψ).app X).hom) ≫
        ((L.comp R T V (φ ≫ ψ) ξ).app X).hom =
      ((L.comp S T V ψ ξ).app ((F R S φ).extension.complex.obj X)).hom ≫
        ((L.comp R S V φ (ψ ≫ ξ)).app X).hom ≫
        eqToHom (congrArg
          (fun f : R ⟶ V ↦ (F R V f).extension.complex.obj X)
          (Category.assoc φ ψ ξ).symm)

/-- Inserting an identity extension before extension gives the same contraction.
Source: Stacks 03CY, 03CZ and 0A8X; the corresponding node equation
(blueprint: lem-sfb-scalar-hom-chain-coefficient-coherence). -/
def CoefficientHomIteration.left_unit_law
    {F : ∀ (R S : Sheaf J CommRingCat.{max c v u}) (φ : R ⟶ S),
      NormalizedCoefficientMaps.{c, v, u} φ}
    (L : CoefficientExtensionAssociators.{c, v, u} F) : Prop :=
  ∀ (R S : Sheaf J CommRingCat.{max c v u})
    (φ : R ⟶ S) (X : Complex.{c, v, u} R),
    ((L.comp R R S (𝟙 R) φ).app X).hom ≫
        eqToHom (congrArg (fun f : R ⟶ S ↦ (F R S f).extension.complex.obj X)
          (Category.id_comp φ)) =
      (F R S φ).extension.complex.map (((L.unit R).app X).hom)

/-- Inserting an identity extension after extension gives the same contraction.
Source: Stacks 03CY, 03CZ and 0A8X; the corresponding node equation
(blueprint: lem-sfb-scalar-hom-chain-coefficient-coherence). -/
def CoefficientHomIteration.right_unit_law
    {F : ∀ (R S : Sheaf J CommRingCat.{max c v u}) (φ : R ⟶ S),
      NormalizedCoefficientMaps.{c, v, u} φ}
    (L : CoefficientExtensionAssociators.{c, v, u} F) : Prop :=
  ∀ (R S : Sheaf J CommRingCat.{max c v u})
    (φ : R ⟶ S) (X : Complex.{c, v, u} R),
    ((L.comp R S S φ (𝟙 S)).app X).hom ≫
        eqToHom (congrArg (fun f : R ⟶ S ↦ (F R S f).extension.complex.obj X)
          (Category.comp_id φ)) =
      ((L.unit S).app ((F R S φ).extension.complex.obj X)).hom

/-- Nu for identity coefficients becomes the identity tensor identification.
Source: Stacks 03CY, 03CZ and 0A8X; the corresponding node equation
(blueprint: lem-sfb-scalar-hom-chain-coefficient-coherence). -/
def CoefficientHomIteration.nu_id_law
    {F : ∀ (R S : Sheaf J CommRingCat.{max c v u}) (φ : R ⟶ S),
      NormalizedCoefficientMaps.{c, v, u} φ}
    (L : CoefficientExtensionAssociators.{c, v, u} F) : Prop :=
  ∀ (R : Sheaf J CommRingCat.{max c v u}) (X : Complex.{c, v, u} R),
    ((F R R (𝟙 R)).chains.nu.app X).hom ≫
        (restriction.{c, v, u} (𝟙 R)).map (((L.unit R).app X).hom) ≫
        ((L.resUnit R).app X).hom =
      ((L.tensorUnit R).app X).hom

/-- Chi for identity coefficients becomes the identity Hom comparison.
Source: Stacks 03CY, 03CZ and 0A8X; the corresponding node equation
(blueprint: lem-sfb-scalar-hom-chain-coefficient-coherence). -/
def CoefficientHomIteration.chi_id_law
    {F : ∀ (R S : Sheaf J CommRingCat.{max c v u}) (φ : R ⟶ S),
      NormalizedCoefficientMaps.{c, v, u} φ}
    (L : CoefficientExtensionAssociators.{c, v, u} F) : Prop :=
  ∀ (R : Sheaf J CommRingCat.{max c v u}) (P A : Complex.{c, v, u} R),
    (F R R (𝟙 R)).homComparison P A ≫
        homMap.{c, v, u} (((L.unit R).app P).inv) (((L.unit R).app A).hom) =
      ((L.unit R).app (homComplex (R := R) P A)).hom

/-- Theta for identity coefficients is the identity after unit identifications.
Source: Stacks 03CY, 03CZ and 0A8X; the corresponding node equation
(blueprint: lem-sfb-scalar-hom-chain-coefficient-coherence). -/
def CoefficientHomIteration.theta_id_law
    {F : ∀ (R S : Sheaf J CommRingCat.{max c v u}) (φ : R ⟶ S),
      NormalizedCoefficientMaps.{c, v, u} φ}
    (L : CoefficientExtensionAssociators.{c, v, u} F) : Prop :=
  ∀ (R : Sheaf J CommRingCat.{max c v u}) (P N : Complex.{c, v, u} R),
    ((F R R (𝟙 R)).chains.theta P N).hom ≫
        homMap.{c, v, u} (𝟙 P) (((L.resUnit R).app N).hom) =
      ((L.resUnit R).app
        (homComplex (R := R) ((F R R (𝟙 R)).extension.complex.obj P) N)).hom ≫
        homMap.{c, v, u} (((L.unit R).app P).inv) (𝟙 N)

/-- Alpha for identity coefficients is the identity after tensor unit contraction.
Source: Stacks 03CY, 03CZ and 0A8X; the corresponding node equation
(blueprint: lem-sfb-scalar-hom-chain-coefficient-coherence). -/
def CoefficientHomIteration.alpha_id_law
    {F : ∀ (R S : Sheaf J CommRingCat.{max c v u}) (φ : R ⟶ S),
      NormalizedCoefficientMaps.{c, v, u} φ}
    (L : CoefficientExtensionAssociators.{c, v, u} F) : Prop :=
  ∀ (R : Sheaf J CommRingCat.{max c v u}) (P A : Complex.{c, v, u} R),
    (F R R (𝟙 R)).alpha P A ≫
        homMap.{c, v, u} (𝟙 P) (((L.tensorUnit R).app A).hom) =
      ((L.tensorUnit R).app (homComplex (R := R) P A)).hom

/-- Sigma for identity coefficients is composition with its arbitrary target map.
Source: Stacks 03CY, 03CZ and 0A8X; the corresponding node equation
(blueprint: lem-sfb-scalar-hom-chain-coefficient-coherence). -/
def CoefficientHomIteration.sigma_id_law
    {F : ∀ (R S : Sheaf J CommRingCat.{max c v u}) (φ : R ⟶ S),
      NormalizedCoefficientMaps.{c, v, u} φ}
    (L : CoefficientExtensionAssociators.{c, v, u} F) : Prop :=
  ∀ (R : Sheaf J CommRingCat.{max c v u}) (P A N : Complex.{c, v, u} R)
    (q : (F R R (𝟙 R)).extension.complex.obj A ⟶ N),
    (F R R (𝟙 R)).sigma P A N q ≫ homMap.{c, v, u} (((L.unit R).app P).inv) (𝟙 N) =
      ((L.unit R).app (homComplex (R := R) P A)).hom ≫
        homMap.{c, v, u} (𝟙 P) ((((L.unit R).app A).inv) ≫ q)

/-- Nu respects contraction of an iterated scalar tensor.
Source: Stacks 03CY, 03CZ and 0A8X; the corresponding node equation
(blueprint: lem-sfb-scalar-hom-chain-coefficient-coherence). -/
def CoefficientHomIteration.nu_comp_law
    {F : ∀ (R S : Sheaf J CommRingCat.{max c v u}) (φ : R ⟶ S),
      NormalizedCoefficientMaps.{c, v, u} φ}
    (L : CoefficientExtensionAssociators.{c, v, u} F) : Prop :=
  ∀ (R S T : Sheaf J CommRingCat.{max c v u})
    (φ : R ⟶ S) (ψ : S ⟶ T) (X : Complex.{c, v, u} R),
    L.underlyingComp φ ψ X ≫ (restriction.{c, v, u} φ).map
        (((F S T ψ).chains.nu.app ((F R S φ).extension.complex.obj X)).hom) =
      ((F R T (φ ≫ ψ)).chains.nu.app X).hom ≫
        ((L.resComp R S T φ ψ).app ((F R T (φ ≫ ψ)).extension.complex.obj X)).inv ≫
        (restriction.{c, v, u} φ).map
          ((restriction.{c, v, u} ψ).map (((L.comp R S T φ ψ).app X).inv))

/-- Successive Hom comparisons contract to the direct Hom comparison.
Source: Stacks 03CY, 03CZ and 0A8X; the corresponding node equation
(blueprint: lem-sfb-scalar-hom-chain-coefficient-coherence). -/
def CoefficientHomIteration.chi_comp_law
    {F : ∀ (R S : Sheaf J CommRingCat.{max c v u}) (φ : R ⟶ S),
      NormalizedCoefficientMaps.{c, v, u} φ}
    (L : CoefficientExtensionAssociators.{c, v, u} F) : Prop :=
  ∀ (R S T : Sheaf J CommRingCat.{max c v u})
    (φ : R ⟶ S) (ψ : S ⟶ T) (P A : Complex.{c, v, u} R),
    (F S T ψ).extension.complex.map ((F R S φ).homComparison P A) ≫
        (F S T ψ).homComparison ((F R S φ).extension.complex.obj P)
          ((F R S φ).extension.complex.obj A) ≫
        homMap.{c, v, u} (((L.comp R S T φ ψ).app P).inv)
          (((L.comp R S T φ ψ).app A).hom) =
      ((L.comp R S T φ ψ).app (homComplex (R := R) P A)).hom ≫
        (F R T (φ ≫ ψ)).homComparison P A

/-- Successive adjunction maps evaluate at the same twice-inserted unit.
Source: Stacks 03CY, 03CZ and 0A8X; the corresponding node equation
(blueprint: lem-sfb-scalar-hom-chain-coefficient-coherence). -/
def CoefficientHomIteration.theta_comp_law
    {F : ∀ (R S : Sheaf J CommRingCat.{max c v u}) (φ : R ⟶ S),
      NormalizedCoefficientMaps.{c, v, u} φ}
    (L : CoefficientExtensionAssociators.{c, v, u} F) : Prop :=
  ∀ (R S T : Sheaf J CommRingCat.{max c v u})
    (φ : R ⟶ S) (ψ : S ⟶ T) (P : Complex.{c, v, u} R) (N : Complex.{c, v, u} T),
    (restriction.{c, v, u} φ).map
        (((F S T ψ).chains.theta ((F R S φ).extension.complex.obj P) N).hom) ≫
        ((F R S φ).chains.theta P ((restriction.{c, v, u} ψ).obj N)).hom ≫
        homMap.{c, v, u} (𝟙 P) (((L.resComp R S T φ ψ).app N).hom) =
      ((L.resComp R S T φ ψ).app (homComplex (R := T)
        ((F S T ψ).extension.complex.obj ((F R S φ).extension.complex.obj P)) N)).hom ≫
        (restriction.{c, v, u} (φ ≫ ψ)).map
          (homMap.{c, v, u} (((L.comp R S T φ ψ).app P).inv) (𝟙 N)) ≫
        ((F R T (φ ≫ ψ)).chains.theta P N).hom

/-- Alpha commutes with contraction of the iterated tensor and Hom evaluation.
Source: Stacks 03CY, 03CZ and 0A8X; the corresponding node equation
(blueprint: lem-sfb-scalar-hom-chain-coefficient-coherence). -/
def CoefficientHomIteration.alpha_comp_law
    {F : ∀ (R S : Sheaf J CommRingCat.{max c v u}) (φ : R ⟶ S),
      NormalizedCoefficientMaps.{c, v, u} φ}
    (L : CoefficientExtensionAssociators.{c, v, u} F) : Prop :=
  ∀ (R S T : Sheaf J CommRingCat.{max c v u})
    (φ : R ⟶ S) (ψ : S ⟶ T) (P A : Complex.{c, v, u} R),
    (F R T (φ ≫ ψ)).alpha P A ≫
        homMap.{c, v, u} (𝟙 P) (L.underlyingComp φ ψ A) =
      L.underlyingComp φ ψ (homComplex (R := R) P A) ≫
        (restriction.{c, v, u} φ).map
          ((tensor.{c, v, u} ψ).map ((F R S φ).homComparison P A)) ≫
        (restriction.{c, v, u} φ).map
          ((F S T ψ).alpha ((F R S φ).extension.complex.obj P)
            ((F R S φ).extension.complex.obj A)) ≫
        ((F R S φ).chains.theta P
          ((tensor.{c, v, u} ψ).obj ((F R S φ).extension.complex.obj A))).hom

/-- Successive sigma agrees for any target and any compatible chain map.
Source: Stacks 03CY, 03CZ and 0A8X; the corresponding node equation
(blueprint: lem-sfb-scalar-hom-chain-coefficient-coherence). -/
def CoefficientHomIteration.sigma_comp_law
    {F : ∀ (R S : Sheaf J CommRingCat.{max c v u}) (φ : R ⟶ S),
      NormalizedCoefficientMaps.{c, v, u} φ}
    (L : CoefficientExtensionAssociators.{c, v, u} F) : Prop :=
  ∀ (R S T : Sheaf J CommRingCat.{max c v u})
    (φ : R ⟶ S) (ψ : S ⟶ T) (P A : Complex.{c, v, u} R)
    (N : Complex.{c, v, u} T)
    (q : (F S T ψ).extension.complex.obj ((F R S φ).extension.complex.obj A) ⟶ N),
    (F S T ψ).extension.complex.map ((F R S φ).homComparison P A) ≫
        (F S T ψ).sigma ((F R S φ).extension.complex.obj P)
          ((F R S φ).extension.complex.obj A) N q ≫
        homMap.{c, v, u} (((L.comp R S T φ ψ).app P).inv) (𝟙 N) =
      ((L.comp R S T φ ψ).app (homComplex (R := R) P A)).hom ≫
        (F R T (φ ≫ ψ)).sigma P A N ((((L.comp R S T φ ψ).app A).inv) ≫ q)

/-- Composition of the supplied normalized maps is direct scalar change.
Source: Stacks 03CY, 03CZ and 0A8X, node proof steps 8 and 10
(blueprint: lem-sfb-scalar-hom-chain-coefficient-coherence). -/
structure CoefficientHomIteration
    {F : ∀ (R S : Sheaf J CommRingCat.{max c v u}) (φ : R ⟶ S),
      NormalizedCoefficientMaps.{c, v, u} φ}
    (L : CoefficientExtensionAssociators.{c, v, u} F) : Prop where
  /-- Both contractions of three scalar extensions agree. -/
  associativity : CoefficientHomIteration.associativity_law L
  /-- Inserting an identity extension before extension gives the same contraction. -/
  left_unit : CoefficientHomIteration.left_unit_law L
  /-- Inserting an identity extension after extension gives the same contraction. -/
  right_unit : CoefficientHomIteration.right_unit_law L
  /-- Nu for identity coefficients becomes the identity tensor identification. -/
  nu_id : CoefficientHomIteration.nu_id_law L
  /-- Chi for identity coefficients becomes the identity Hom comparison. -/
  chi_id : CoefficientHomIteration.chi_id_law L
  /-- Theta for identity coefficients is the identity after unit identifications. -/
  theta_id : CoefficientHomIteration.theta_id_law L
  /-- Alpha for identity coefficients is the identity after tensor unit contraction. -/
  alpha_id : CoefficientHomIteration.alpha_id_law L
  /-- Sigma for identity coefficients is composition with its arbitrary target map. -/
  sigma_id : CoefficientHomIteration.sigma_id_law L
  /-- Nu respects contraction of an iterated scalar tensor. -/
  nu_comp : CoefficientHomIteration.nu_comp_law L
  /-- Successive Hom comparisons contract to the direct Hom comparison. -/
  chi_comp : CoefficientHomIteration.chi_comp_law L
  /-- Successive adjunction maps evaluate at the same twice-inserted unit. -/
  theta_comp : CoefficientHomIteration.theta_comp_law L
  /-- Alpha commutes with contraction of the iterated tensor and Hom evaluation. -/
  alpha_comp : CoefficientHomIteration.alpha_comp_law L
  /-- Successive sigma agrees for any target and any compatible chain map. -/
  sigma_comp : CoefficientHomIteration.sigma_comp_law L
```

Each `*_law` is exactly the former field type, with the same binders and
conclusion. They are transparent definitions in this module, attached to the
existing node. Existing equation getters retain their names and applications.
The original five inverse formulas are now public proved theorems:
`unit_inv`, `resUnit_inv`, `tensorUnit_inv`, `comp_inv`, `resComp_inv`, in the
`CoefficientExtensionAssociators` namespace. Apply the inverse to the forward
formula at scalar 1 and use `hom_inv_id`; the composition case additionally uses
`map_one` and `mul_one`. Thus a record of the old type restricts to a repaired
record, and the five theorems recover every omitted field. Proof irrelevance
identifies recovered proof fields. The formulations have the same mathematical
content, including identity maps, zero objects, and noninvertible ring maps.

The original theorem signature is unchanged. Its complete proof constructs
extension comparisons using `Adjunction.leftAdjointUniq`, transfers the existing
proved normalized coefficient squares using uniqueness of normalized maps,
and verifies pasting and Hom iteration on actual local tensor generators.

Local proof commands activate `ordinaryExtension_additive` as a local instance,
keep the tensor and product-Hom definitions abstract, and open
`NormalizedCoefficientSquare.tensorComparison` only for the Data adapter proof.
Private helpers use proof-only `import all` directives. No global instance or
public import is added. No axiom, unsafe declaration, opaque declaration, or
unfinished definition is introduced.

## Users

`tools/downstream.py Sheaf.Algebra.Homology.ScalarHomChainCoefficientCoherence`
reports zero downstream modules. Its `--uses CoefficientExtensionAssociators`
query reports only the item itself. The unfinished DAG parents and unit route
are retained, and no module is withdrawn. Definition review for any target
using these records is requested: the forward and derived inverse equations
are mathematically equivalent to the original fields. No consumer needs an
adaptation, and no other group's module is changed.

| module | group holding it | effect |
| --- | --- | --- |
| `Sheaf.Algebra.Homology.ScalarHomChainCoefficientCoherence` | A8 | Shares equation types; derives inverse laws; constructs the remaining forward fields; proves the sole original hole. |

## Status

landed 20261023T230356-L-3419170 2026-10-23 (merge of deliver/A8/Sheaf.Algebra.Homology.ScalarHomChainCoefficientCoherence)
