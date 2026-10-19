## Worker report

The module `lean/Sheaf/TraceFormula/MittagLefflerEventualDomination.lean` states the
Stacks Tag 059E characterization of tensor-product Mittag--Leffler modules.  It uses a
small directed partially ordered index `I` with `[Nonempty I]` and
`[IsDirected I (· ≤ ·)]`, a functor `F : I ⥤ ModuleCat R` giving the modules and
transition maps, a cocone `c`, and `hc : IsColimit c`; `c.pt` is the colimit module.
The stage finite-presentation clause is rendered by
`[∀ i : I, Module.FinitePresentation R (F.obj i)]`.

The left side is exactly `Module.IsMittagLeffler R c.pt`, the tensor-product condition
from `def-trf-mittag-leffler-module`, including every set/family of test modules in its
recorded definition.  The right side says `∀ i : I, ∃ j : I, i ≤ j`; the transition map
`f_ij` is `((F.map (homOfLE hij)).hom)`, and the canonical map `f_i` is
`((c.ι.app i).hom)`.  For every test `R`-module `L` in `Type (max u v t)`, domination is
rendered clause-for-clause as
`LinearMap.ker ((c.ι.app i).hom.rTensor L) ≤
LinearMap.ker ((F.map (homOfLE hij)).hom.rTensor L)`, i.e. the required tensor-kernel
inclusion.  The universal quantifiers include zero modules and empty index families;
`Nonempty I` records the directed-system convention and no additional hypotheses are
introduced.

The dependency declarations used are:

- `Sheaf.RingTheory.IsMittagLeffler`, `Module.IsMittagLeffler` (the tensor-product
  definition node `def-trf-mittag-leffler-module`).
- `CategoryTheory.Limits.colimit`, `Cocone`, `IsColimit`, and `CategoryTheory.IsFiltered`
  (the Mathlib node `def-weil-pbc-category-colimit`; the statement uses the explicit
  cocone form rather than an arbitrary chosen object).
- `Mathlib.Algebra.Module.FinitePresentation`, `Module.FinitePresentation` (the
  Mathlib node `def-sc-finitely-presented-module`).
- `Sheaf.RingTheory.MittagLefflerHomSystems`,
  `Module.hom_images_stabilize_of_isMittagLeffler`, imported because it is a stated
  proof dependency and supplies the forward stabilization step.

Edge cases checked: `I` is required nonempty; a one-object system with identity maps
satisfies the displayed eventual clause; zero stages and zero test modules make both
kernel inclusions well-typed; the empty family in `Module.IsMittagLeffler` is covered by
its universal quantifier; and the index universe `Type v` is the module-category
universe, while test modules use `Type (max u v t)` so no smaller independent universe
makes the condition vacuous.

Searches made: `msearch.py leanfinder` for “maps of modules b dominates a tensor kernel
inclusion” (no matching theorem); `msearch.py loogle` for “LinearMap ker tensorProduct”
(no Mittag--Leffler characterization); `msearch.py grep` for `MittagLeffler|dominates`
in Mathlib (no match); `rg` over `WeilConjectures/` and project `lean/Sheaf/` for
Mittag--Leffler/eventual-domination declarations (only the dependency modules and no
this theorem); and `grep` over DAG nodes for the item id (no duplicate declaration).
The module compiled cleanly with `scompile.py`; the only postponed proof is the named
statement theorem itself.

## Second reading by NL

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

## Maintainer fix (independent review, 2026-10-18)

The delivered statement was right in substance, but it fixed the stage-module universe at
`ModuleCat.{max u v} R`, which ties the stage modules to the ring and index universes. The
recorded dependency `Module.hom_images_stabilize_of_isMittagLeffler` does not do this; it
uses `ModuleCat.{max u v w} R`. The fix adds the free universe `w`:
`F : I ⥤ ModuleCat.{max u v w} R`,
`Module.IsMittagLeffler.{u, max u v w, max u v w, t} R c.pt`, and
`L : Type (max u v w t)`. The Mittag--Leffler index sets range over the stage-module
universe, which is the size the hom-systems dependency uses. The delivered statement is
the case `w = 0`. The docstring now gives the node's seven proof steps (H8), with the
DAG dependencies each step uses. The worker report's edge-case remark about the index
universe is superseded by this section.
