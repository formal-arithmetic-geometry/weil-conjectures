/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.FineSaturatedLogBlowup
public import Sheaf.AlgebraicGeometry.LogMorphismOperations

/-!
# Dense-open isomorphism of a fixed saturated logarithmic blowup tower

Source: ILO VI 1.2, 1.6--1.7; VIII 3.3.8--3.3.11 and 3.4.8
(blueprint: lem-per-saturated-log-tower-dense-open).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- A fixed saturated log blowup tower with log regular endpoints is an isomorphism
between dense opens. No projectivity, terminal freeness or integralness is assumed.

Source: ILO VI 1.2, 1.6--1.7; VIII 3.3.8--3.3.11 and 3.4.8
(blueprint: lem-per-saturated-log-tower-dense-open).

Proof:
1. For a log regular fs log scheme, its trivial-characteristic locus is open: on a
finite chart it is the intersection of the unit loci of the finitely many monoid
generators. These opens descend through the open etale chart maps. It is dense:
at every component generic point the local ring, and hence its strict henselization,
has dimension zero. The log regular dimension equality forces characteristic rank
zero. A sharp saturated monoid has torsion-free group completion, finitely generated
by the chart generators. A finite free abelian group of rational rank zero is trivial;
integrality embeds the characteristic monoid in it. Thus all generic points belong
to the triviality locus. This proves density for both endpoints, including empty ones.
2. For one saturated blowup use its saturated fraction charts Q_e^sat inside P^gp.
If the images of P are units, so are their ratios and all saturated elements: an
element with a unit positive power is a unit. Conversely units in the source chart
force all P-images to be units. The local ring map reflects units, so the target
characteristic is trivial. Consequently the source triviality locus is exactly the
inverse image of the target triviality locus.
3. Over the triviality locus any nonempty coherent log ideal is the whole unit
monoid, hence already invertible. The universal property of the saturated log
blowup supplies the inverse of its restriction there; uniqueness shows both
composites are identities, on schemes as well as log sections. The chart
construction commutes with strict open restriction, so this applies to every arrow.
4. Iterate the restricted isomorphisms along the finite tower. The equations on p
identify the resulting scheme map with its terminal composite. Use the two endpoint
triviality opens from step 1 for U and W. Their inclusions commute with the restricted
isomorphism, giving the displayed equality. At length zero use the identity. -/
theorem saturatedLogTower_denseOpen
    (T : SaturatedLogBlowupTower.{u})
    (p : ∀ i : Fin (T.length + 1), EtaleLogHom (T.level i) (T.level 0))
    (hp0 : p 0 = EtaleLogHom.id (T.level 0))
    (hp : ∀ i : Fin T.length, (T.arrow i).CompEq (p i.castSucc) (p i.succ))
    (hstart : (T.level 0).IsLogRegular)
    (hfinish : (T.level (Fin.last T.length)).IsLogRegular) :
    ∃ (U : (T.level (Fin.last T.length)).scheme.Opens)
      (W : (T.level 0).scheme.Opens) (e : U.toScheme ≅ W.toScheme),
      Dense (U : Set (T.level (Fin.last T.length)).scheme) ∧
      Dense (W : Set (T.level 0).scheme) ∧
      U.ι ≫ (p (Fin.last T.length)).base = e.hom ≫ W.ι := by sorry

end AlgebraicGeometry
