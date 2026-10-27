# Profinite.CondensedAction.PolynomialRankOne data-module extraction

## Reason

The finite-system construction and the scalar-extended internal presentation are distinct
parts of the assigned proof. Both need its existing PolynomialSystem and
PresentationAssertion interfaces. Extract those interfaces to a foundational module so
the two split statements can be imported by the original theorem without an import cycle.
The original module publicly reexports all extracted declarations. The moved declarations
have identical names, signatures, visibility, fields and bodies; only their blueprint
ownership comments now refer to the definition node. No statement or definition has been
weakened, and no object is chosen from either split theorem.

## Old

In Sheaf.Paper.PolynomialRankOneDifferenceModel, the data block was:

```lean
/-- The y and spectator z variables, with y_1 indexed by zero.
Source: polynomial filtration (3)
(blueprint: lem-sfb-polynomial-rank-one-difference-model). -/
abbrev Variables (k m : ℕ) := Fin (k + 1) ⊕ Fin m

/-- The actual bounded-degree monomial index, including the constant monomial.
Source: polynomial filtration (3)
(blueprint: lem-sfb-polynomial-rank-one-difference-model). -/
abbrev Indices (k m n : ℕ) := {d : Variables k m →₀ ℕ // d.sum (fun _ a ↦ a) ≤ n}

/-- Residual translation in y_2,...,y_r, retaining its inverse-limit topology.
Source: splitting the first coordinate in (3)
(blueprint: lem-sfb-polynomial-rank-one-difference-model). -/
abbrev Residual (ℓ k : ℕ) [Fact ℓ.Prime] := Fin k → IntegerGroup.{u} ℓ

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type u) [NormedField E]
  [NormedAlgebra ℚ_[ℓ] E] (k m : ℕ)

/-- The scalar coordinates in the order y_1,y_2,...,y_r.
Source: translation formula (3)
(blueprint: lem-sfb-polynomial-rank-one-difference-model). -/
def coordinates (g : Residual.{u} ℓ k × IntegerGroup.{u} ℓ) : Fin (k + 1) → E :=
  Fin.cases (algebraMap ℚ_[ℓ] E (g.2.toAdd.down : ℚ_[ℓ]))
    (fun i ↦ algebraMap ℚ_[ℓ] E ((g.1 i).toAdd.down : ℚ_[ℓ]))

/-- Actual substitution, translating only the y variables by negative coordinates.
Source: translation formula (3)
(blueprint: lem-sfb-polynomial-rank-one-difference-model). -/
def translate (g : Residual.{u} ℓ k × IntegerGroup.{u} ℓ) :
    MvPolynomial (Variables k m) E →ₐ[E] MvPolynomial (Variables k m) E :=
  MvPolynomial.aeval (Sum.elim
    (fun i ↦ MvPolynomial.X (Sum.inl i) - MvPolynomial.C (coordinates ℓ E k g i))
    (fun i ↦ MvPolynomial.X (Sum.inr i)))

/-- The finite-stage system with its exact polynomial identification and monomial basis.
The image condition specifies V_n, rather than an arbitrary finite representation.
Source: finite polynomial stages and Taylor formula in (3)
(blueprint: lem-sfb-polynomial-rank-one-difference-model). -/
structure PolynomialSystem where
  system : System ℓ E (Residual.{u} ℓ k)
  embed : ∀ n : ℕ, system.V n →ₗ[E] MvPolynomial (Variables k m) E
  injective : ∀ n : ℕ, Function.Injective (embed n)
  image : ∀ (n : ℕ) (f : MvPolynomial (Variables k m) E),
    (∃ v : system.V n, embed n v = f) ↔
      ∀ d ∈ f.support, d.sum (fun _ a ↦ a) ≤ n
  finiteIndices : ∀ n : ℕ, Finite (Indices k m n)
  basis : ∀ n : ℕ, Module.Basis (Indices k m n) E (system.V n)
  monomials : ∀ (n : ℕ) (d : Indices k m n),
    embed n (basis n d) = MvPolynomial.monomial d.val 1
  inclusion : ∀ (n : ℕ) (v : system.V n),
    embed (n + 1) (system.transition n v) = embed n v
  derivative : ∀ (n : ℕ) (v : system.V n),
    embed n (system.operator n v) = -MvPolynomial.pderiv (Sum.inl 0) (embed n v)
  exponent : ∀ n : ℕ, system.exponent n = n + 1
  translation : ∀ (n : ℕ) (g : Residual.{u} ℓ k × IntegerGroup.{u} ℓ) (v : system.V n),
    embed n (system.action n g v) = translate ℓ E k m g (embed n v)
  polynomialEntries : ∀ (n : ℕ) (a b : Indices k m n),
    ∃ p : MvPolynomial (Fin (k + 1)) E,
      ∀ g : Residual.{u} ℓ k × IntegerGroup.{u} ℓ,
        (basis n).repr (system.action n g (basis n b)) a =
          MvPolynomial.eval (coordinates ℓ E k g) p
  matrixContinuous : ∀ (n : ℕ) (a b : Indices k m n),
    Continuous (fun g : Residual.{u} ℓ k × IntegerGroup.{u} ℓ ↦
      (basis n).repr (system.action n g (basis n b)) a)

variable (F : Type u) [NormedField F] [NormedAlgebra ℚ_[ℓ] F] [Algebra E F]

/-- The actual scalar-extended polynomial embedding, used for coefficient projections.
Source: tensoring the monomial basis in (3)
(blueprint: lem-sfb-polynomial-rank-one-difference-model). -/
def tensorPolynomial (Q : PolynomialSystem ℓ E k m) (n : ℕ)
    (v : Extended E F (Q.system.V n)) : MvPolynomial (Variables k m) F :=
  MvPolynomial.scalarRTensorAlgEquiv ((Q.embed n).baseChange F v)

/-- Evaluate a finite polynomial as a generalized monomial section of the existing T.
Source: monomial coprojections in (3)
(blueprint: lem-sfb-polynomial-rank-one-difference-model). -/
def polynomialSection (T : PolynomialTranslation.Model ℓ F (k + 1) m)
    (S : Profinite.{u}) (p : MvPolynomial (Variables k m) F)
    (c : ULift.{u + 1} C(S, F)) : sectionModule (normContinuousRing F) T.object.module S :=
  ∑ d ∈ p.support, ((T.ι d).hom.hom.app (op S)).hom
    (ULift.up (ContinuousMap.const S (p.coeff d)) * c)

/-- The complete internal presentation, including its coefficient projections and
its normalized colimit isomorphism. The pointwise group formula identifies the split
G x H with the original rank-r lattice. The last equations identify D, exp(D), and
Delta as internal maps on every generalized monomial section.
Source: finite sub-sums, colimit and difference identity in (3)
(blueprint: lem-sfb-polynomial-rank-one-difference-model). -/
def PresentationAssertion (Q : PolynomialSystem ℓ E k m) : Prop :=
  ∃ π : Residual.{u} ℓ k × IntegerGroup.{u} ℓ →ₜ*
      Multiplicative (ULift.{u} (Fin (k + 1) → ℤ_[ℓ])),
    (∀ g : Residual.{u} ℓ k × IntegerGroup.{u} ℓ,
      (π g).toAdd.down = Fin.cases g.2.toAdd.down (fun i ↦ (g.1 i).toAdd.down)) ∧
    ∀ T : PolynomialTranslation.Model ℓ F (k + 1) m,
    ∃ P : IndUnipotent.Presentation ℓ E F (Residual.{u} ℓ k) Q.system,
    ∃ w : ∀ n : ℕ, (P.stage n).object ⟶ (inflate π).obj T.object,
    ∃ j : ∀ n : ℕ, Indices k m n →
        (Mod.regular (normContinuousRing F).X ⟶ (P.stage n).object.module),
    ∃ p : ∀ n : ℕ, Indices k m n →
        ((P.stage n).object.module ⟶ Mod.regular (normContinuousRing F).X),
      (∀ n : ℕ, Nonempty (IsColimit (Cofan.mk (P.stage n).object.module (j n)))) ∧
      (∀ (n : ℕ) (d : Indices k m n), j n d ≫ (w n).val = T.ι d.val) ∧
      (∀ (n : ℕ) (d : Indices k m n) (S : Profinite.{u})
        (a : ULift.{u + 1} C(S, F)) (s : S),
        (((P.stage n).sections S
          (((j n d).hom.hom.app (op S)).hom a)).down s) =
            a.down s ⊗ₜ[E] (Q.basis n d)) ∧
      (∀ (n : ℕ) (d : Indices k m n) (S : Profinite.{u})
        (v : sectionModule (normContinuousRing F) (P.stage n).object.module S) (s : S),
        (((p n d).hom.hom.app (op S)).hom v).down s =
          (tensorPolynomial ℓ E k m F Q n (((P.stage n).sections S v).down s)).coeff d.val) ∧
      (∀ n : ℕ, (P.identify n).hom ≫ w n =
        P.diagram.map (homOfLE (Nat.le_succ n)) ≫ (P.identify (n + 1)).hom ≫ w (n + 1)) ∧
      ∃ c : Cocone P.diagram, Nonempty (IsColimit c) ∧
        Nonempty (IsColimit ((forgetAction).mapCocone c)) ∧
      ∃ e : c.pt ≅ (inflate π).obj T.object,
        (∀ n : ℕ, c.ι.app n ≫ e.hom = (P.identify n).hom ≫ w n) ∧
      ∃ (D expD delta : (inflate π).obj T.object ⟶ (inflate π).obj T.object),
        (∀ (n : ℕ) (S : Profinite.{u})
          (v : sectionModule (normContinuousRing F) (P.stage n).object.module S),
          ∃ v' : sectionModule (normContinuousRing F) (P.stage n).object.module S,
            (∀ s : S, (((P.stage n).sections S v').down s) =
              ((Q.system.operator n).baseChange F) (((P.stage n).sections S v).down s)) ∧
            (D.val.hom.hom.app (op S)).hom (((w n).val.hom.hom.app (op S)).hom v) =
              ((w n).val.hom.hom.app (op S)).hom v') ∧
        (∀ (n : ℕ) (S : Profinite.{u})
          (v : sectionModule (normContinuousRing F) (P.stage n).object.module S),
          (expD.val.hom.hom.app (op S)).hom (((w n).val.hom.hom.app (op S)).hom v) =
            ((w n).val.hom.hom.app (op S)).hom
              ((P.stage n).object.act S (ContinuousMap.const S (1, generator ℓ)) v)) ∧
        (∀ (S : Profinite.{u}) (d : Variables k m →₀ ℕ) (a : ULift.{u + 1} C(S, F)),
          (D.val.hom.hom.app (op S)).hom (((T.ι d).hom.hom.app (op S)).hom a) =
            polynomialSection ℓ k m F T S
              (-MvPolynomial.pderiv (Sum.inl 0) (MvPolynomial.monomial d 1)) a) ∧
        expD - 𝟙 _ = delta ∧
        (∀ (S : Profinite.{u})
          (v : sectionModule (normContinuousRing F) T.object.module S),
          (delta.val.hom.hom.app (op S)).hom v =
            @Sub.sub (sectionModule (normContinuousRing F) T.object.module S) inferInstance
              (((inflate π).obj T.object).act S
                (ContinuousMap.const S (1, generator ℓ)) v) v) ∧
        (∀ (S : Profinite.{u}) (d : Variables k m →₀ ℕ) (a : ULift.{u + 1} C(S, F)),
          (delta.val.hom.hom.app (op S)).hom (((T.ι d).hom.hom.app (op S)).hom a) =
            polynomialSection ℓ k m F T S
              (translate ℓ F k m (1, generator ℓ) (MvPolynomial.monomial d 1) -
                MvPolynomial.monomial d 1) a)
```

## New

The identical data block, with the blueprint ownership comment updated, is in
Sheaf.Paper.PolynomialRankOneDifferenceModelData:

```lean
/-- The y and spectator z variables, with y_1 indexed by zero.
Source: polynomial filtration (3)
(blueprint: def-sfb-polynomial-rank-one-model-data). -/
abbrev Variables (k m : ℕ) := Fin (k + 1) ⊕ Fin m

/-- The actual bounded-degree monomial index, including the constant monomial.
Source: polynomial filtration (3)
(blueprint: def-sfb-polynomial-rank-one-model-data). -/
abbrev Indices (k m n : ℕ) := {d : Variables k m →₀ ℕ // d.sum (fun _ a ↦ a) ≤ n}

/-- Residual translation in y_2,...,y_r, retaining its inverse-limit topology.
Source: splitting the first coordinate in (3)
(blueprint: def-sfb-polynomial-rank-one-model-data). -/
abbrev Residual (ℓ k : ℕ) [Fact ℓ.Prime] := Fin k → IntegerGroup.{u} ℓ

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type u) [NormedField E]
  [NormedAlgebra ℚ_[ℓ] E] (k m : ℕ)

/-- The scalar coordinates in the order y_1,y_2,...,y_r.
Source: translation formula (3)
(blueprint: def-sfb-polynomial-rank-one-model-data). -/
def coordinates (g : Residual.{u} ℓ k × IntegerGroup.{u} ℓ) : Fin (k + 1) → E :=
  Fin.cases (algebraMap ℚ_[ℓ] E (g.2.toAdd.down : ℚ_[ℓ]))
    (fun i ↦ algebraMap ℚ_[ℓ] E ((g.1 i).toAdd.down : ℚ_[ℓ]))

/-- Actual substitution, translating only the y variables by negative coordinates.
Source: translation formula (3)
(blueprint: def-sfb-polynomial-rank-one-model-data). -/
def translate (g : Residual.{u} ℓ k × IntegerGroup.{u} ℓ) :
    MvPolynomial (Variables k m) E →ₐ[E] MvPolynomial (Variables k m) E :=
  MvPolynomial.aeval (Sum.elim
    (fun i ↦ MvPolynomial.X (Sum.inl i) - MvPolynomial.C (coordinates ℓ E k g i))
    (fun i ↦ MvPolynomial.X (Sum.inr i)))

/-- The finite-stage system with its exact polynomial identification and monomial basis.
The image condition specifies V_n, rather than an arbitrary finite representation.
Source: finite polynomial stages and Taylor formula in (3)
(blueprint: def-sfb-polynomial-rank-one-model-data). -/
structure PolynomialSystem where
  system : System ℓ E (Residual.{u} ℓ k)
  embed : ∀ n : ℕ, system.V n →ₗ[E] MvPolynomial (Variables k m) E
  injective : ∀ n : ℕ, Function.Injective (embed n)
  image : ∀ (n : ℕ) (f : MvPolynomial (Variables k m) E),
    (∃ v : system.V n, embed n v = f) ↔
      ∀ d ∈ f.support, d.sum (fun _ a ↦ a) ≤ n
  finiteIndices : ∀ n : ℕ, Finite (Indices k m n)
  basis : ∀ n : ℕ, Module.Basis (Indices k m n) E (system.V n)
  monomials : ∀ (n : ℕ) (d : Indices k m n),
    embed n (basis n d) = MvPolynomial.monomial d.val 1
  inclusion : ∀ (n : ℕ) (v : system.V n),
    embed (n + 1) (system.transition n v) = embed n v
  derivative : ∀ (n : ℕ) (v : system.V n),
    embed n (system.operator n v) = -MvPolynomial.pderiv (Sum.inl 0) (embed n v)
  exponent : ∀ n : ℕ, system.exponent n = n + 1
  translation : ∀ (n : ℕ) (g : Residual.{u} ℓ k × IntegerGroup.{u} ℓ) (v : system.V n),
    embed n (system.action n g v) = translate ℓ E k m g (embed n v)
  polynomialEntries : ∀ (n : ℕ) (a b : Indices k m n),
    ∃ p : MvPolynomial (Fin (k + 1)) E,
      ∀ g : Residual.{u} ℓ k × IntegerGroup.{u} ℓ,
        (basis n).repr (system.action n g (basis n b)) a =
          MvPolynomial.eval (coordinates ℓ E k g) p
  matrixContinuous : ∀ (n : ℕ) (a b : Indices k m n),
    Continuous (fun g : Residual.{u} ℓ k × IntegerGroup.{u} ℓ ↦
      (basis n).repr (system.action n g (basis n b)) a)

variable (F : Type u) [NormedField F] [NormedAlgebra ℚ_[ℓ] F] [Algebra E F]

/-- The actual scalar-extended polynomial embedding, used for coefficient projections.
Source: tensoring the monomial basis in (3)
(blueprint: def-sfb-polynomial-rank-one-model-data). -/
def tensorPolynomial (Q : PolynomialSystem ℓ E k m) (n : ℕ)
    (v : Extended E F (Q.system.V n)) : MvPolynomial (Variables k m) F :=
  MvPolynomial.scalarRTensorAlgEquiv ((Q.embed n).baseChange F v)

/-- Evaluate a finite polynomial as a generalized monomial section of the existing T.
Source: monomial coprojections in (3)
(blueprint: def-sfb-polynomial-rank-one-model-data). -/
def polynomialSection (T : PolynomialTranslation.Model ℓ F (k + 1) m)
    (S : Profinite.{u}) (p : MvPolynomial (Variables k m) F)
    (c : ULift.{u + 1} C(S, F)) : sectionModule (normContinuousRing F) T.object.module S :=
  ∑ d ∈ p.support, ((T.ι d).hom.hom.app (op S)).hom
    (ULift.up (ContinuousMap.const S (p.coeff d)) * c)

/-- The complete internal presentation, including its coefficient projections and
its normalized colimit isomorphism. The pointwise group formula identifies the split
G x H with the original rank-r lattice. The last equations identify D, exp(D), and
Delta as internal maps on every generalized monomial section.
Source: finite sub-sums, colimit and difference identity in (3)
(blueprint: def-sfb-polynomial-rank-one-model-data). -/
def PresentationAssertion (Q : PolynomialSystem ℓ E k m) : Prop :=
  ∃ π : Residual.{u} ℓ k × IntegerGroup.{u} ℓ →ₜ*
      Multiplicative (ULift.{u} (Fin (k + 1) → ℤ_[ℓ])),
    (∀ g : Residual.{u} ℓ k × IntegerGroup.{u} ℓ,
      (π g).toAdd.down = Fin.cases g.2.toAdd.down (fun i ↦ (g.1 i).toAdd.down)) ∧
    ∀ T : PolynomialTranslation.Model ℓ F (k + 1) m,
    ∃ P : IndUnipotent.Presentation ℓ E F (Residual.{u} ℓ k) Q.system,
    ∃ w : ∀ n : ℕ, (P.stage n).object ⟶ (inflate π).obj T.object,
    ∃ j : ∀ n : ℕ, Indices k m n →
        (Mod.regular (normContinuousRing F).X ⟶ (P.stage n).object.module),
    ∃ p : ∀ n : ℕ, Indices k m n →
        ((P.stage n).object.module ⟶ Mod.regular (normContinuousRing F).X),
      (∀ n : ℕ, Nonempty (IsColimit (Cofan.mk (P.stage n).object.module (j n)))) ∧
      (∀ (n : ℕ) (d : Indices k m n), j n d ≫ (w n).val = T.ι d.val) ∧
      (∀ (n : ℕ) (d : Indices k m n) (S : Profinite.{u})
        (a : ULift.{u + 1} C(S, F)) (s : S),
        (((P.stage n).sections S
          (((j n d).hom.hom.app (op S)).hom a)).down s) =
            a.down s ⊗ₜ[E] (Q.basis n d)) ∧
      (∀ (n : ℕ) (d : Indices k m n) (S : Profinite.{u})
        (v : sectionModule (normContinuousRing F) (P.stage n).object.module S) (s : S),
        (((p n d).hom.hom.app (op S)).hom v).down s =
          (tensorPolynomial ℓ E k m F Q n (((P.stage n).sections S v).down s)).coeff d.val) ∧
      (∀ n : ℕ, (P.identify n).hom ≫ w n =
        P.diagram.map (homOfLE (Nat.le_succ n)) ≫ (P.identify (n + 1)).hom ≫ w (n + 1)) ∧
      ∃ c : Cocone P.diagram, Nonempty (IsColimit c) ∧
        Nonempty (IsColimit ((forgetAction).mapCocone c)) ∧
      ∃ e : c.pt ≅ (inflate π).obj T.object,
        (∀ n : ℕ, c.ι.app n ≫ e.hom = (P.identify n).hom ≫ w n) ∧
      ∃ (D expD delta : (inflate π).obj T.object ⟶ (inflate π).obj T.object),
        (∀ (n : ℕ) (S : Profinite.{u})
          (v : sectionModule (normContinuousRing F) (P.stage n).object.module S),
          ∃ v' : sectionModule (normContinuousRing F) (P.stage n).object.module S,
            (∀ s : S, (((P.stage n).sections S v').down s) =
              ((Q.system.operator n).baseChange F) (((P.stage n).sections S v).down s)) ∧
            (D.val.hom.hom.app (op S)).hom (((w n).val.hom.hom.app (op S)).hom v) =
              ((w n).val.hom.hom.app (op S)).hom v') ∧
        (∀ (n : ℕ) (S : Profinite.{u})
          (v : sectionModule (normContinuousRing F) (P.stage n).object.module S),
          (expD.val.hom.hom.app (op S)).hom (((w n).val.hom.hom.app (op S)).hom v) =
            ((w n).val.hom.hom.app (op S)).hom
              ((P.stage n).object.act S (ContinuousMap.const S (1, generator ℓ)) v)) ∧
        (∀ (S : Profinite.{u}) (d : Variables k m →₀ ℕ) (a : ULift.{u + 1} C(S, F)),
          (D.val.hom.hom.app (op S)).hom (((T.ι d).hom.hom.app (op S)).hom a) =
            polynomialSection ℓ k m F T S
              (-MvPolynomial.pderiv (Sum.inl 0) (MvPolynomial.monomial d 1)) a) ∧
        expD - 𝟙 _ = delta ∧
        (∀ (S : Profinite.{u})
          (v : sectionModule (normContinuousRing F) T.object.module S),
          (delta.val.hom.hom.app (op S)).hom v =
            @Sub.sub (sectionModule (normContinuousRing F) T.object.module S) inferInstance
              (((inflate π).obj T.object).act S
                (ContinuousMap.const S (1, generator ℓ)) v) v) ∧
        (∀ (S : Profinite.{u}) (d : Variables k m →₀ ℕ) (a : ULift.{u + 1} C(S, F)),
          (delta.val.hom.hom.app (op S)).hom (((T.ι d).hom.hom.app (op S)).hom a) =
            polynomialSection ℓ k m F T S
              (translate ℓ F k m (1, generator ℓ) (MvPolynomial.monomial d 1) -
                MvPolynomial.monomial d 1) a)
```

The original module publicly imports the new data module and privately imports the two
split proof modules. Its theorem statement is unchanged. The old public imports remain
publicly reexported through the data module. The two unused private imports
Mathlib.Data.Nat.Choose.Sum and Mathlib.Topology.Algebra.Module.FiniteDimension are removed.

## Users

The direct-importer search and tools/downstream.py find no current Lean importer of the
item module. The DAG's unfinished parents still require the theorem; they are retained.
The original data and theorem remain available at their original names via public import.
No existing module other than the assigned item is modified.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.PolynomialRankOneDifferenceModel | A6 | Same public data and theorem statement; theorem proved from two split statements. |
| Sheaf.Paper.PolynomialRankOneDifferenceModelData | A6, new | Owns the unchanged data block and public imports. |
| Sheaf.Paper.PolynomialRankOneSystemExistence | A6, new | Uses the finite-system interface for its construction statement. |
| Sheaf.Paper.PolynomialRankOnePresentation | A6, new | Uses the system and presentation interfaces for one arbitrary coefficient extension. |

## Status

landed 20261026T080838-L-1626806 2026-10-26 (merge of deliver/A6/Sheaf.Paper.PolynomialRankOneDifferenceModel)
