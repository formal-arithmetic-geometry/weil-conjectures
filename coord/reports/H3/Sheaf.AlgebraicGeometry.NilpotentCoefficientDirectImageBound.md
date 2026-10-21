## What changed

Proved `AlgebraicGeometry.Etale.isZero_higherDirectImage_of_nilpotent_quotient_bound`
with its signature unchanged. The proof constructs the descending presheaf filtration
`P_j(U) = I^j M(U)`, proves its quotient short exact sequences componentwise, and
sheafifies them. The existing `ModuleCat.quotSMulTop` construction supplies honest
quotient coefficient actions. Restriction of scalars commutes with sheafification by
its adjunction to coextension, giving the quotient sheaves to which the stated
coefficient-change theorem applies. The existing single-object comparison and full
long exact sequence reduce each induction step to exactness between two zero objects.
Descending induction starts at `P_t = 0` and ends at `P_0 ≅ M`.

All added constructions and helper theorems are private and fully proved. The two
public imports and every public declaration signature remain unchanged. The DAG proof
now records this filtration and the actual supporting declarations. Its unit statement
and unit route remain unchanged. No other module or public interface changes.

The new proof imports are `WeilConjectures.Algebra.Category.ModuleCat.QuotSMulTop`,
`WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusSingle`, and
`Mathlib.Algebra.Homology.ShortComplex.ModuleCat`.

Validation: the complete Lean proof compiled cleanly through `lcompile.py` in 42.9 seconds.
The delivery command also recompiles the final file with its axiom/hole probe and preflight.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Etale.isZero_higherDirectImage_of_nilpotent_quotient_bound`
(node `lem-sf-nilpotent-coefficient-direct-image-bound`). No holes added or split off;
no `sorry` remains in this delivery. Existing hypotheses on quotient higher direct
images and the library's stated long-exact-sequence theorem are used as intended.

The proof keeps the degree fixed, and so includes `N < 0`, `q = 0`, `t = 1`, zero
coefficient rings, and the empty scheme. Neither finite generation nor flatness is
used.

## No longer needed

Removed these private imports:

- `Mathlib.CategoryTheory.Sites.ConstantSheaf`: no constant-sheaf construction occurs
  in the proof; the two original public imports still provide the statement context.
- `Sheaf.CategoryTheory.RingedSiteModules`: the construction works directly with
  `Sheaf J (ModuleCat R)` and uses exact sheafification.
- `Sheaf.AlgebraicGeometry.EtaleConstantModuleDirectImageLeftExact`: its theorem uses
  the alternative `SheafOfModules` encoding. The existing `lowerStar` additive and
  finite-limit-preservation instances work directly with the encoding of this item.
- `Sheaf.AlgebraicGeometry.EtaleModuleEnoughInjectives`: its module assertion also uses
  the alternative encoding. The source's generic Grothendieck-abelian sheaf instance
  and Mathlib's enough-injectives instance supply the needed hypothesis directly.

Accordingly removed direct proof dependencies on
`def-weil-pbc-constant-sheaf`, `def-weil-sheaf-of-modules-category`,
`lem-weil-pbc-module-direct-image-left-exact`, and
`lem-weil-pbc-module-sheaves-enough-injectives`. The last two obsolete `tool_uses`
entries were removed. These are local dependency prunings only; no source declaration
or module is withdrawn, and these results may still have other consumers.

The replacement supporting nodes are the existing
`lem-weil-pbc-sheaf-tensor-closed` (only its Grothendieck-abelian and exact-sheafification
clause), `lem-sp-grothendieck-enough-injectives`,
`lem-weil-pbc-direct-image-left-exact` (its recorded generic `lowerStar` instances),
and `lem-sp-derived-functor-single-identification`. They are already stated and
recorded as source-proved or Mathlib leaves; no new mathematical task is introduced.

## Where the brief, the DAG or earlier work was wrong

The planned annihilator filtration is valid, but the descending ideal-power
filtration fits the available `ModuleCat.quotSMulTop` API more directly. Sheafifying
presheaf short exact sequences avoids constructing annihilator subsheaf gluing and
quotient actions over constant ring sheaves separately. The old enough-injectives
and module-direct-image declarations have the alternative module-sheaf encoding;
the generic source instances apply to the theorem's actual encoding.

Read Stacks `derived.tex`, `lemma-higher-derived-functors` (Tag 015B), and
`sites-modules.tex`, `lemma-abelian` (Tag 03DA) and `lemma-sheafification-exact`
(Tag 03EI), and `sites-cohomology.tex`, `lemma-cohomology-modules-abelian-agree`
(Tag 03FD). The statement needs no correction.
There are no new nodes, definition repairs, or forced adaptations.

## Second reading by H3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
