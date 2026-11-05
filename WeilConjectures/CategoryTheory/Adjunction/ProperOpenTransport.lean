/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Adjunction.MateComparisonTransport
public import Mathlib.CategoryTheory.Adjunction.Whiskering

/-!
# Transport of open base change and clopen projections

Comparison functors compatible with inverse images carry the unit-transpose open base-change
comparison, the open-to-direct-image comparison and the clopen projection to their
counterparts, the open extensions being compared by the mates of the inverse-image
comparisons.

Source: Weil conjectures blueprint, node thm-cbc-complete-proetale, proof step 8
(blueprint: thm-cbc-complete-proetale).
-/

@[expose] public noncomputable section

open CategoryTheory Functor

namespace CategoryTheory.ProperOpenTransport

section BetaInv

variable {U U' X X' : Type*} [Category U] [Category U'] [Category X] [Category X']
  {U₁ U₁' X₁ X₁' : Type*} [Category U₁] [Category U₁'] [Category X₁] [Category X₁']

end BetaInv

section OpenToPush

variable {U X U₁ X₁ : Type*} [Category U] [Category X] [Category U₁] [Category X₁]
  {J : U ⥤ X} {P : X ⥤ U} {R : U ⥤ X} (adjJ : J ⊣ P) (adjP : P ⊣ R) [IsIso adjJ.unit]
  {J₁ : U₁ ⥤ X₁} {P₁ : X₁ ⥤ U₁} {R₁ : U₁ ⥤ X₁} (adjJ₁ : J₁ ⊣ P₁) (adjP₁ : P₁ ⊣ R₁)
  [IsIso adjJ₁.unit]

variable {ΦU : U ⥤ U₁} {ΦX : X ⥤ X₁} (φ : P ⋙ ΦU ≅ ΦX ⋙ P₁)

end OpenToPush

section Alpha

variable {DS DT DW DV DP : Type*} [Category DS] [Category DT] [Category DW] [Category DV]
  [Category DP]
  {Ji : DS ⥤ DT} {Pi : DT ⥤ DS} (adjI : Ji ⊣ Pi) {Pp : DT ⥤ DW} {Psnd : DS ⥤ DP}
  {Jfst : DP ⥤ DW} {Pfst : DW ⥤ DP} (adjFst : Jfst ⊣ Pfst)
  {Js : DV ⥤ DP} {Ps : DP ⥤ DV} {Rs : DV ⥤ DP} (adjS : Js ⊣ Ps) (adjPs : Ps ⊣ Rs)
  [IsIso adjS.unit] [IsIso (openToPush adjS adjPs)]
  {Jk : DV ⥤ DW} {Pr : DS ⥤ DV}
  (sq : Pp ⋙ Pfst ≅ Pi ⋙ Psnd) [∀ x, IsIso (betaInvApp adjI adjFst sq x)]
  (c : Js ⋙ Jfst ≅ Jk) (e : Psnd ⋙ Ps ≅ Pr)

variable {DS' DT' DW' DV' DP' : Type*} [Category DS'] [Category DT'] [Category DW']
  [Category DV'] [Category DP']
  {Ji' : DS' ⥤ DT'} {Pi' : DT' ⥤ DS'} (adjI' : Ji' ⊣ Pi') {Pp' : DT' ⥤ DW'}
  {Psnd' : DS' ⥤ DP'} {Jfst' : DP' ⥤ DW'} {Pfst' : DW' ⥤ DP'} (adjFst' : Jfst' ⊣ Pfst')
  {Js' : DV' ⥤ DP'} {Ps' : DP' ⥤ DV'} {Rs' : DV' ⥤ DP'} (adjS' : Js' ⊣ Ps')
  (adjPs' : Ps' ⊣ Rs') [IsIso adjS'.unit] [IsIso (openToPush adjS' adjPs')]
  {Jk' : DV' ⥤ DW'} {Pr' : DS' ⥤ DV'}
  (sq' : Pp' ⋙ Pfst' ≅ Pi' ⋙ Psnd') [∀ x, IsIso (betaInvApp adjI' adjFst' sq' x)]
  (c' : Js' ⋙ Jfst' ≅ Jk') (e' : Psnd' ⋙ Ps' ≅ Pr')
  {ΦS : DS ⥤ DS'} {ΦT : DT ⥤ DT'} {ΦW : DW ⥤ DW'} {ΦV : DV ⥤ DV'} {ΦP : DP ⥤ DP'}
  (φi : Pi ⋙ ΦS ≅ ΦT ⋙ Pi') (φp : Pp ⋙ ΦW ≅ ΦT ⋙ Pp')
  (φsnd : Psnd ⋙ ΦP ≅ ΦS ⋙ Psnd') (φfst : Pfst ⋙ ΦP ≅ ΦW ⋙ Pfst')
  (φs : Ps ⋙ ΦV ≅ ΦP ⋙ Ps') (φr : Pr ⋙ ΦV ≅ ΦS ⋙ Pr')
  [IsIso (openComparison adjI adjI' φi)] [IsIso (openComparison adjFst adjFst' φfst)]
  [IsIso (openComparison adjS adjS' φs)]

end Alpha

section AbstractAlpha

variable {DS DT DW DV DP : Type*} [iDS : Category DS] [iDT : Category DT] [iDW : Category DW]
  [iDV : Category DV] [iDP : Category DP]
  {Ji : DS ⥤ DT} {Pp : DT ⥤ DW} {Psnd : DS ⥤ DP} {Jfst : DP ⥤ DW} {Ps : DP ⥤ DV}
  {Js : DV ⥤ DP} {Jk Jsf : DV ⥤ DW} {Pr Psr : DS ⥤ DV}

variable {Pi : DT ⥤ DS} (adjI : Ji ⊣ Pi) {Pfst : DW ⥤ DP} (adjFst : Jfst ⊣ Pfst)
  {Rs : DV ⥤ DP} (adjS : Js ⊣ Ps) (adjPs : Ps ⊣ Rs)
  [IsIso adjS.unit] [IsIso (openToPush adjS adjPs)]
  (sq : Pp ⋙ Pfst ≅ Pi ⋙ Psnd) [∀ x, IsIso (betaInvApp adjI adjFst sq x)]

end AbstractAlpha

section Square

variable {CT CS CW CV CT' CS' CW' CV' : Type*} [Category CT] [Category CS] [Category CW]
  [Category CV] [Category CT'] [Category CS'] [Category CW'] [Category CV']
  {Pi : CT ⥤ CS} {Pr : CS ⥤ CV} {Pp : CT ⥤ CW} {Pk : CW ⥤ CV} {Pri Pkp : CT ⥤ CV}
  {Pi' : CT' ⥤ CS'} {Pr' : CS' ⥤ CV'} {Pp' : CT' ⥤ CW'} {Pk' : CW' ⥤ CV'}
  {Pri' Pkp' : CT' ⥤ CV'}
  {ΦT : CT ⥤ CT'} {ΦS : CS ⥤ CS'} {ΦW : CW ⥤ CW'} {ΦV : CV ⥤ CV'}

end Square

section Gamma

variable {DS DT DW DV DP : Type*} [iDS : Category DS] [iDT : Category DT] [iDW : Category DW]
  [iDV : Category DV] [iDP : Category DP]
  {Ji : DS ⥤ DT} {Pi : DT ⥤ DS} (adjI : Ji ⊣ Pi) {Pp : DT ⥤ DW} {Rp : DW ⥤ DT}
  (adjP : Pp ⊣ Rp) {Psnd : DS ⥤ DP}
  {Jfst : DP ⥤ DW} {Pfst : DW ⥤ DP} (adjFst : Jfst ⊣ Pfst)
  {Js : DV ⥤ DP} {Ps : DP ⥤ DV} {Rs : DV ⥤ DP} (adjS : Js ⊣ Ps) (adjPs : Ps ⊣ Rs)
  [IsIso adjS.unit] [IsIso (openToPush adjS adjPs)]
  {Jk : DV ⥤ DW} {Pr : DS ⥤ DV} {Rr : DV ⥤ DS} (adjR : Pr ⊣ Rr)
  (sq : Pp ⋙ Pfst ≅ Pi ⋙ Psnd) [∀ x, IsIso (betaInvApp adjI adjFst sq x)]
  (c : Js ⋙ Jfst ≅ Jk) (e : Psnd ⋙ Ps ≅ Pr)
  {DS' DT' DW' DV' DP' : Type*} [iDS' : Category DS'] [iDT' : Category DT']
  [iDW' : Category DW'] [iDV' : Category DV'] [iDP' : Category DP']
  {Ji' : DS' ⥤ DT'} {Pi' : DT' ⥤ DS'} (adjI' : Ji' ⊣ Pi') {Pp' : DT' ⥤ DW'}
  {Rp' : DW' ⥤ DT'} (adjP' : Pp' ⊣ Rp')
  {Psnd' : DS' ⥤ DP'} {Jfst' : DP' ⥤ DW'} {Pfst' : DW' ⥤ DP'} (adjFst' : Jfst' ⊣ Pfst')
  {Js' : DV' ⥤ DP'} {Ps' : DP' ⥤ DV'} {Rs' : DV' ⥤ DP'} (adjS' : Js' ⊣ Ps')
  (adjPs' : Ps' ⊣ Rs') [IsIso adjS'.unit] [IsIso (openToPush adjS' adjPs')]
  {Jk' : DV' ⥤ DW'} {Pr' : DS' ⥤ DV'} {Rr' : DV' ⥤ DS'} (adjR' : Pr' ⊣ Rr')
  (sq' : Pp' ⋙ Pfst' ≅ Pi' ⋙ Psnd') [∀ x, IsIso (betaInvApp adjI' adjFst' sq' x)]
  (c' : Js' ⋙ Jfst' ≅ Jk') (e' : Psnd' ⋙ Ps' ≅ Pr')
  {ΦS : DS ⥤ DS'} {ΦT : DT ⥤ DT'} {ΦW : DW ⥤ DW'} {ΦV : DV ⥤ DV'} {ΦP : DP ⥤ DP'}
  (φi : Pi ⋙ ΦS ≅ ΦT ⋙ Pi') (φp : Pp ⋙ ΦW ≅ ΦT ⋙ Pp')
  (φsnd : Psnd ⋙ ΦP ≅ ΦS ⋙ Psnd') (φfst : Pfst ⋙ ΦP ≅ ΦW ⋙ Pfst')
  (φs : Ps ⋙ ΦV ≅ ΦP ⋙ Ps') (φr : Pr ⋙ ΦV ≅ ΦS ⋙ Pr')
  [IsIso (openComparison adjI adjI' φi)] [IsIso (openComparison adjFst adjFst' φfst)]
  [IsIso (openComparison adjS adjS' φs)]
  [IsIso (mateEquiv adjR adjR' φr.inv)] [IsIso (mateEquiv adjP adjP' φp.inv)]

end Gamma

end CategoryTheory.ProperOpenTransport
