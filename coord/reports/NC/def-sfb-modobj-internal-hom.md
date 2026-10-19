## Worker report

The delivery reuses the existing equalizer internal hom, its target action and its
functorial maps, and states the missing adjunction with the actual relative monoidal
tensor. Its module is `Sheaf.CategoryTheory.Monoidal.ModuleEqualizerInternalHom`; its
sole new declaration is
`CategoryTheory.Mod.nonempty_equalizerInternalHomAdjunction`, with proof `sorry`.
The node's Lean record is mixed: the existing definitions are listed together with
this new theorem. No definition or monoidal structure is copied or replaced.

The definition part of the node already exists in
`WeilConjectures.CategoryTheory.Monoidal.Mod.InternalHom`: `Mod.ihom' R M`.
It cannot alone be an exact existing-only attachment for the whole node: the
adjunction `Mod.ihom'Adjunction` uses `Mod.tensorLeft M`, whose value at L is the
separate coequalizer computing L tensor_R M. The node requires the specific
monoidal structure of `def-sfb-modobj-relative-tensor`, and M tensor_R L.
Conversely, `Mod.monoidalClosed` in the current published
`WeilConjectures.CategoryTheory.ModuleObjects.GrothendieckAbelian` uses an
abstract adjoint-functor-theorem right adjoint, without identifying that choice
with the node's equalizer. The new theorem supplies exactly this missing link;
its right functor is the real upstream equalizer, never an unspecified functor.
`Nonempty (F ⊣ G)` asserts the existence of a natural adjunction with BOTH functors
fixed. It is not used to choose any data, canonical map, internal hom or instance.
The existing closedness instance is recorded too, rather than defined again.

Hypothesis and clause correspondence:

| Node text | Lean rendering |
| --- | --- |
| Ambient category C | `{C : Type u} [Category.{v} C]`; u and v are explicit and independent. |
| Grothendieck abelian | `[Abelian C] [IsGrothendieckAbelian.{v} C]`, following the dependency's Mathlib match. |
| Symmetric monoidal | `[MonoidalCategory C] [SymmetricCategory C]`. |
| Tensor additive in both variables | `[MonoidalPreadditive C]`. |
| Closed; ambient right adjoint of X tensor - | `[MonoidalClosed C]`; upstream `CategoryTheory.ihom X`, `ihom.adjunction X`, and `ihom.ev X`. |
| Commutative monoid object R | `(R : C) [MonObj R] [IsCommMonObj R]`. |
| R-modules M and N | `(M : Mod C R)` and the argument `N : Mod C R` of the functor `ihom' R M`. N is universally the functor/adjunction's target variable, not restricted. |
| Ambient Hom(M,N) and Hom(R tensor M,N) | `(CategoryTheory.ihom M.X).obj N.X` and `(CategoryTheory.ihom (R ⊗ M.X)).obj N.X` in `homMod` and `homModB`. |
| First displayed arrow, through action on N | `homModB R M N`, with underlying map `curry ((α_ R M.X _).hom ≫ R ◁ (CategoryTheory.ihom.ev M.X).app N.X ≫ act N.X)`. |
| Second displayed arrow, through action on M | `homModPre (act M.X) N`; underlying map `(MonoidalClosed.pre (act M.X)).app N.X`, whose uncurry is the action followed by evaluation. |
| The equalizer | `(ihom' R M).obj N = equalizer (homModPre (act M.X) N) (homModB R M N)` by the existing definition. The displayed pair is listed in reverse order, imposing exactly the same equality and equalizer universal property. |
| The equalizer is an object of C with its induced module structure | The equalizer is constructed in `Mod C R`; `Mod.forget R` creates limits via the explicit `limitSMul` construction, so its underlying cone is the specified ambient equalizer. |
| R acts through N | `homAct R M.X N`, the curry of evaluation followed by `act N.X` after interchanging M and R. `homMod` bundles it; the equalizer action is its restriction and the inclusion is linear. |
| Functor Hom_R(M,-) | `ihom' R M`, whose morphism map is the equalizer lift of postcomposition `homModMap M.X f`. |
| Right adjoint to M tensor_R - | The new theorem states `Nonempty (MonoidalCategory.tensorLeft M ⊣ ihom' R M)`. The left functor is literally that of `Mod.monoidalCategory`, not the similarly named `Mod.tensorLeft`. |
| The specified symmetric monoidal category is closed | The theorem applies to every M, yielding a right adjoint for each left tensor functor; `Mod.monoidalClosed` is also the existing closedness instance for this exact monoidal structure. No assumption of closedness on the module category is added. |
| The module category is abelian | Existing `Mod.instAbelian` from the recorded dependency, with preservation of finite colimits supplied by ambient closedness. This is explanatory context, not an added conjunct. |

Dependencies read and used:

- `def-sp-grothendieck-abelian`: `CategoryTheory.IsGrothendieckAbelian` in
  `Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic`, including its
  small-colimit and small-limit instances.
- `sk-def-sfb-module-objects`: the closed slopmaster2 audit identifies Mathlib's
  `CategoryTheory.ModObj`, `CategoryTheory.Mod`, `Mod.forget`, `Mod.regular` in
  `Mathlib.CategoryTheory.Monoidal.Mod`. Their full declarations and action/morphism
  equations were read. The general internal-module category is exactly the one used.
- `def-sfb-modobj-relative-tensor`: `Mod.monoidalCategory` in
  `WeilConjectures.CategoryTheory.ModuleObjects.Monoidal`, read through
  `scompile.py --source` because the older local source lacks that path. Its
  `tensorObj_X`, `tensorObjπ` and action formula identify the precise coequalizer.
- `def-sfb-modobj-symmetric-tensor`: `Mod.braidedCategory`, `Mod.symmetricCategory`
  in `WeilConjectures.CategoryTheory.ModuleObjects.Symmetric`, also read through
  `scompile.py --source`. The descended braiding is needed for the factor order.
- `lem-sfb-modobj-abelian`: the recorded `Mod.instAbelian`, read in
  `WeilConjectures.CategoryTheory.Monoidal.Mod.Abelian` with its assumptions:
  `[Abelian C] [MonoidalPreadditive C] [PreservesFiniteColimits (tensorLeft R)]`.
- Proof prerequisites `def-sp-abelian` and
  `lem-weil-pbc-left-adjoint-preserves-colimits`: `CategoryTheory.Abelian` in
  `Mathlib.CategoryTheory.Abelian.Basic` and
  `Adjunction.leftAdjoint_preservesColimits` in
  `Mathlib.CategoryTheory.Adjunction.Limits`. Both source signatures and docstrings
  were read. They are already imported through the two public imports, as are the
  statement dependencies; no redundant proof imports are added.

Additional upstream construction read in full:
`WeilConjectures.CategoryTheory.Monoidal.Mod.InternalHom`, especially `homAct`,
`homModObj`, `homMod`, `homModPre`, `homModB`, `ihom'`, `ihomLift`, `ihomDesc`,
`ihom'Adjunction`; and the created-limit construction in
`WeilConjectures.CategoryTheory.Monoidal.Mod.Limits`. The current published
GrothendieckAbelian source was inspected through `scompile.py --source` to see
exactly what its `monoidalClosed` constructs. Its private tensor comparison is
not exposed as an API; the new theorem's proof plan records how to reconstruct
that canonical comparison by the coequalizer property in stage 3.

Edge cases checked before writing: M=0 or N=0 gives the expected zero Hom object;
R=the tensor unit recovers the ambient internal hom; the zero ring object permits
its zero module category; nonflat modules and nonreduced/zero-divisor coefficients
are allowed, since the construction uses equalizers and coequalizers, not exactness
of tensor. No nonzero, flatness, finiteness, characteristic or faithfulness
hypothesis is present. The finite parallel-pair diagrams impose no restriction
on indexing universes. The only size convention is the dependency's prescribed
Grothendieck universe v, leaving the object universe u independent. The adjunction
uses the blueprint's M tensor_R L order rather than silently changing it.

Searches (all on 2026-10-18):

- `msearch.py leanfinder`, query `Internal Hom for module objects over a commutative
  monoid in a closed symmetric monoidal category, equalizer of action maps`: eight
  hits, including `ModuleCat.instMonoidalClosed`, ModuleCat evaluation/currying,
  and a representation internal Hom. None states the general internal-module case.
- `msearch.py loogle`, query `CategoryTheory.Mod, CategoryTheory.MonoidalClosed`:
  zero hits.
- `msearch.py grep`, query `ihom|Closed|equalizer`, Mathlib
  `CategoryTheory/Monoidal/Mod.lean`: zero hits.
- `msearch.py leansearch`, query `Internal hom of module objects over commutative
  monoid equalizer tensor adjunction`: eight hits on the ambient adjunction and
  ordinary ModuleCat, no exact module-object equalizer adjunction.
- `msearch.py grep`, query `equalizerInternalHomAdjunction|ihom.*Adjunction`, Mathlib
  `CategoryTheory/Monoidal`: 23 ambient-closedness hits, no internal-module bridge.
- `rg --files` in upstream CategoryTheory found the current `Monoidal/Mod` files;
  `rg` for internalHom/ihom/adjunction in them found the existing concrete
  construction and `ihom'Adjunction`, which are reused as described above.
- `rg` for `def-sfb-modobj-internal-hom` in upstream WeilConjectures: no hits.
- `rg` in `dag/lean_names_upstream.json` for module closedness/internal Hom names:
  the snapshot index did not carry these new current declarations; direct source
  inspection and `scompile.py --source` resolved them.
- `rg` in `lean/Sheaf` for `ihom'Adjunction`, `homModB`, `homModPre` and equalizer
  adjunctions: no existing general bridge. Specialized sheaf internal Homs and
  the etale finite-projective comparison import the upstream construction.

No statement correction, disputed statement, new definition node or dependency
repair is needed. The existing node fields other than `lean` are unchanged.

Validation: the module compiled through the prescribed `scompile.py NC
 def-sfb-modobj-internal-hom ...` wrapper, both sandbox and library passes,
without errors or warnings (1.3 s and 1.5 s). Every universe and variable is
explicitly bound. The only new proof is exactly `sorry`; all construction data
is the existing upstream data. The file has no line longer than 89 characters.

## Author check

Re-read the source node and the delivery together. The initial API mismatch is
important: `Mod.tensorLeft` is not `MonoidalCategory.tensorLeft`, and upstream
`monoidalClosed` alone does not fix its chosen right adjoint to be the equalizer.
The delivered signature explicitly uses `MonoidalCategory.tensorLeft` and
`Mod.ihom'`, retaining both the source's tensor structure and its concrete Hom.
All five statement dependencies and both additional proof prerequisites are
available through the imports. No independent worker reading is claimed here;
the maintainer performs the independent review under the dispatcher's instructions.

## Second reading by NC

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
