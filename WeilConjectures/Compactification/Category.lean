/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib
public import WeilConjectures.Compactification.Defs

/-!

# The category of compactifications of a morphism

For a morphism of schemes `f : X ⟶ Y`, this file endows the type
`AlgebraicGeometry.Compactification f` of compactifications `X ⟶[i] Z ⟶[g] Y` of `f` with
the structure of a category and records its cofilteredness.

A morphism of compactifications `u : c' ⟶ c` is a morphism `u : c'.Z ⟶ c.Z` over `Y`
restricting to the identity on `X`, such that the square

```
    X  ==== X
c'.i|       |c.i
    v       v
  c'.Z --> c.Z
        u
```

is **Cartesian**. The Cartesian condition says that `X` is exactly the preimage of `X` in
the finer compactification; it is what makes the extension by zero along `c'.i` push
forward to the extension by zero along `c.i` (see
`WeilConjectures.SixFunctors.LowerShriek.CompactificationInvariance`). The morphism `u` is
automatically proper (`Compactification.Hom.isProper`), being a morphism from a proper
`Y`-scheme to a separated one.

Under the usual hypotheses (here: `f` quasi-compact and admitting a compactification at
all), the category of compactifications is **cofiltered**:

- it is nonempty (`HasCompactification f`);
- any two compactifications admit a common refinement
  (`Compactification.exists_refinement`, currently `sorry`ed): take the schematic closure
  of `X` in `c.Z ×_Y d.Z`;
- any two parallel morphisms of compactifications are equalized by a further refinement
  (`Compactification.exists_hom_equalizing`, currently `sorry`ed): two morphisms
  `c' ⟶ c` agree on the dense open `X`, hence on the schematic closure of `X` in `c'.Z`,
  which is itself a refinement of `c'`.

The cofilteredness is what produces the *canonical* comparison isomorphisms between the
lower shrieks defined via different compactifications; the third condition in particular
makes the comparison independent of the choice of common refinement.

## Main definitions

- `AlgebraicGeometry.Compactification.Hom`: morphisms of compactifications.
- The instance `Category (Compactification f)`.
- `AlgebraicGeometry.Compactification.Hom.isProper`: a morphism of compactifications is
  proper.
- The instance `IsCofiltered (Compactification f)`, assembled from the two `sorry`ed
  existence lemmas above.

-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

namespace Compactification

variable {X Y : Scheme.{u}} {f : X ⟶ Y}

/-- A morphism of compactifications `c' ⟶ c` of `f : X ⟶ Y`: a morphism `c'.Z ⟶ c.Z`
over `Y` restricting to the identity on `X`, such that the square

```
    X  ==== X
c'.i|       |c.i
    v       v
  c'.Z --> c.Z
```

is Cartesian. The commutation `c'.i ≫ hom = c.i` is part of `isPullback`; it is recorded
separately as `Compactification.Hom.i_hom`. -/
structure Hom (c' c : Compactification f) where
  /-- The underlying morphism between the compactifying schemes. -/
  hom : c'.Z ⟶ c.Z
  /-- The morphism is a morphism over `Y`. -/
  w : hom ≫ c.g = c'.g
  /-- The square formed by the two open immersions, the identity on `X` and `hom` is
  Cartesian: `X` is the preimage of `X` under `hom`. -/
  isPullback : IsPullback c'.i (𝟙 X) hom c.i

namespace Hom

variable {c'' c' c : Compactification f}

lemma ext {u v : Hom c' c} (h : u.hom = v.hom) : u = v := by
  cases u
  cases v
  subst h
  rfl

/-- A morphism of compactifications restricts to the identity on `X`. -/
@[reassoc]
lemma i_hom (u : Hom c' c) : c'.i ≫ u.hom = c.i := by
  simpa using u.isPullback.w

end Hom

instance : Category (Compactification f) where
  Hom := Hom
  id c := ⟨𝟙 c.Z, by simp, IsPullback.id_vert c.i⟩
  comp u v := ⟨u.hom ≫ v.hom, by rw [Category.assoc, v.w, u.w],
    by simpa using u.isPullback.paste_vert v.isPullback⟩
  id_comp u := Hom.ext (Category.id_comp u.hom)
  comp_id u := Hom.ext (Category.comp_id u.hom)
  assoc u v w := Hom.ext (Category.assoc u.hom v.hom w.hom)

variable {c'' c' c : Compactification f}

@[ext]
lemma hom_ext {u v : c' ⟶ c} (h : u.hom = v.hom) : u = v := Hom.ext h

@[simp]
lemma id_hom (c : Compactification f) : Hom.hom (𝟙 c) = 𝟙 c.Z := rfl

@[simp]
lemma comp_hom (u : c'' ⟶ c') (v : c' ⟶ c) : (u ≫ v).hom = u.hom ≫ v.hom := rfl

/-- A morphism of compactifications is proper: it is a morphism from a proper `Y`-scheme
to a separated one. -/
instance Hom.isProper (u : c' ⟶ c) : IsProper u.hom :=
  have : IsProper (u.hom ≫ c.g) := by
    rw [u.w]
    exact c'.isProper
  IsProper.of_comp (f := u.hom) (g := c.g)

section Cofiltered

variable (f) in
/-- Any two compactifications of a quasi-compact `f` admit a common refinement: the
schematic closure of `X` in `c.Z ×_Y d.Z`.

The open immersions `X ⟶ c.Z` and `X ⟶ d.Z` combine to an immersion
`X ⟶ c.Z ×_Y d.Z` (the graph factorization through `X ×_Y d.Z` is a closed immersion
since `d.g` is separated, and `X ×_Y d.Z ⟶ c.Z ×_Y d.Z` is an open immersion). Since
`f`, and hence the immersion, is quasi-compact, `X` is open in its schematic closure
`Z''`, which is a closed subscheme of the proper `Y`-scheme `c.Z ×_Y d.Z`, hence proper
over `Y`. The two projections restrict to morphisms of compactifications `Z'' ⟶ c.Z` and
`Z'' ⟶ d.Z`; the Cartesian condition holds because `X` is open in `Z''` and equal to the
preimage of `X` under either projection. -/
theorem exists_refinement [QuasiCompact f] (c d : Compactification f) :
    ∃ (e : Compactification f) (_ : e ⟶ c) (_ : e ⟶ d), True :=
  sorry

/-- Two parallel morphisms of compactifications of a quasi-compact `f` are equalized by a
further refinement: the schematic closure of `X` in `c'.Z`.

Both morphisms restrict to the identity on the open subscheme `X`, whose schematic
closure `e.Z` in `c'.Z` is a refinement of `c'` (here quasi-compactness of the open
immersion `c'.i`, i.e. of `f`, is used again). Since `c.g` is separated, the locus where
the two morphisms agree is a closed subscheme of `c'.Z` containing the schematically
dense `X`, hence contains `e.Z`. -/
theorem exists_hom_equalizing [QuasiCompact f] {c' c : Compactification f}
    (u v : c' ⟶ c) :
    ∃ (e : Compactification f) (w : e ⟶ c'), w ≫ u = w ≫ v :=
  sorry

/-- The category of compactifications of a quasi-compact morphism admitting one is
cofiltered. This is the key structural input for the compactification independence of the
lower shriek: it produces the canonical comparison isomorphisms between the lower shrieks
associated with any two compactifications. -/
instance [HasCompactification f] [QuasiCompact f] : IsCofiltered (Compactification f) where
  cone_objs c d := exists_refinement f c d
  cone_maps _ _ u v := exists_hom_equalizing u v
  nonempty := HasCompactification.nonempty_compactification

end Cofiltered

end Compactification

end AlgebraicGeometry
