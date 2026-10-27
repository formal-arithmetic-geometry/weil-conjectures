/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q52
-/
module

public import Sheaf.AlgebraicGeometry.StrictLogBlowupProcedure

/-!
# Ordered log tower descent data with actual centers

Source: ILO VIII 3.3.7--3.3.10, pp.107--108, and the initial descent assertion
in the proof of 3.3.15, p.109 (blueprint: def-trf-log-tower-center-descent-datum).

The datum is expressed on the represented functors of points. The pair of maps
`a, b` with equal composites to the base is a point of the double overlap.
Naturality makes `transport` the ordered isomorphism of the uncontracted recursive
pullbacks; `diagonal` and `cocycle` are its diagonal and triple-overlap equations.
No pullback objects, maps, or inverses are chosen from an existence theorem.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

namespace AlgebraicGeometry

/-- Points of a specified tower level over a specified point of its initial log scheme.
Source: ILO VIII 3.3.9--3.3.10 (blueprint: def-trf-log-tower-center-descent-datum). -/
def LogTowerPoint {U : FineSaturatedLogScheme.{u}} (S : LogBlowupTowerOver U)
    (i : Fin (S.tower.length + 1)) (T : FineSaturatedLogScheme.{u})
    (a : EtaleLogHom T U) :=
  {s : EtaleLogHom T (S.tower.level i) // s.comp (S.toBase i) = a}

/-- An ordered center-preserving Čech datum, in its equivalent functor-of-points form.
`transport` is the levelwise isomorphism over the double overlap, `arrows` preserves
all ordered arrows, and `centers` preserves the actual ideal subsheaves. The two
identity laws and invertibility are encoded by equivalences, the diagonal equation,
and the cocycle equation. The test objects include the representing fs pullbacks,
so this is the usual datum, without a representability or effectivity assumption.
Source: ILO VIII 3.3.7--3.3.10 and proof of 3.3.15, pp.107--109
(blueprint: def-trf-log-tower-center-descent-datum). -/
structure LogTowerCenterDescentDatum {X U : FineSaturatedLogScheme.{u}}
    (uMap : EtaleLogHom U X) (S : LogBlowupTowerOver U) where
  transport : ∀ (T : FineSaturatedLogScheme.{u}) (a b : EtaleLogHom T U),
    a.comp uMap = b.comp uMap → ∀ i : Fin (S.tower.length + 1),
      LogTowerPoint S i T a ≃ LogTowerPoint S i T b
  naturality : ∀ (T T' : FineSaturatedLogScheme.{u}) (c : EtaleLogHom T' T)
    (a b : EtaleLogHom T U) (h : a.comp uMap = b.comp uMap)
    (h' : (c.comp a).comp uMap = (c.comp b).comp uMap)
    (i : Fin (S.tower.length + 1)) (s : LogTowerPoint S i T a)
    (s' : LogTowerPoint S i T' (c.comp a)),
    s'.val = c.comp s.val →
      (transport T' (c.comp a) (c.comp b) h' i s').val =
        c.comp (transport T a b h i s).val
  diagonal : ∀ (T : FineSaturatedLogScheme.{u}) (a : EtaleLogHom T U)
    (i : Fin (S.tower.length + 1)), transport T a a rfl i = Equiv.refl _
  cocycle : ∀ (T : FineSaturatedLogScheme.{u}) (a b c : EtaleLogHom T U)
    (hab : a.comp uMap = b.comp uMap) (hbc : b.comp uMap = c.comp uMap)
    (i : Fin (S.tower.length + 1)),
    (transport T a b hab i).trans (transport T b c hbc i) =
      transport T a c (hab.trans hbc) i
  arrows : ∀ (T : FineSaturatedLogScheme.{u}) (a b : EtaleLogHom T U)
    (h : a.comp uMap = b.comp uMap) (i : Fin S.tower.length)
    (s : LogTowerPoint S i.succ T a) (s' : LogTowerPoint S i.castSucc T a),
    s'.val = s.val.comp (S.tower.arrow i) →
      (transport T a b h i.castSucc s').val =
        (transport T a b h i.succ s).val.comp (S.tower.arrow i)
  centers : ∀ (T : FineSaturatedLogScheme.{u}) (a b : EtaleLogHom T U)
    (h : a.comp uMap = b.comp uMap) (i : Fin S.tower.length)
    (s : LogTowerPoint S i.castSucc T a),
    s.val.pullbackIdeal (S.tower.center i) =
      (transport T a b h i.castSucc s).val.pullbackIdeal (S.tower.center i)

end AlgebraicGeometry
