# Sheaf.Paper.ECoefficientSmoothBaseChange proof context

## Reason

Stage-3 preflight classifies added commands and instances conservatively as interface
changes and requires a change record. The proof adds local elaboration settings, opens
the tensor notation scope, and introduces private comparison constructions and instances.
Every existing public declaration signature, public definition body, and public import
is unchanged. The two existing theorem proof bodies are completed.

The new instances concern only the private functor `sbcFiniteView`; ordinary importers
cannot refer to that functor. The new irreducible attributes concern private comparison
isomorphisms, preventing their constructions from unfolding during later elaboration.
No mathematical definition or target statement changes meaning.

## Old

The original commands after the module docstring were:

```lean
@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures
```

The original module had no `sbcFiniteView`, its four private instances, or its private
comparison isomorphisms. The public helper and main theorem had `sorry` proofs.

## New

The commands before the proved private helpers are:

```lean
@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped TensorProduct
```

Private helpers are grouped in `AlgebraicGeometry.Scheme`; the existing public declarations
remain in `WeilConjectures`. Private instances `sbcFiniteView_equivalence`, `sbcFiniteView_additive`,
`sbcFiniteView_limits`, and `sbcFiniteView_colimits` provide equivalence, additive, and
exactness APIs for the private coefficient view. Naming exactness avoids repeating
instance synthesis in the derived comparison declarations. Its constructed isomorphisms have `@[irreducible]` attributes.
The existing helper retains its original section parameters; its unused-section-variable
linter setting is scoped to that one declaration:

```lean
set_option linter.unusedSectionVars false in
```

The anonymous public noncomputable section is explicitly closed after
`end WeilConjectures`. This restores the surrounding elaboration options before a
subsequent command (including the delivery tool's appended axiom probe). The proof's
coefficient-presentation transparency settings are confined to the proofs themselves;
no check is removed or given a larger time limit.

The existing public definitions and theorem signatures are identical to the old ones.
All additions support proofs only, with no new public declaration.

## Users

`tools/downstream.py Sheaf.Paper.ECoefficientSmoothBaseChange --uses
 eCoefficientSmoothBaseChange sbcPrimeUnitOnSource` lists the following modules. The
only downstream module is the Qbar-coefficient theorem, which uses the same helper
signature. It requires no adaptation because no public interface changed mathematically.

| module | group holding it | effect |
| --- | --- | --- |
| `Sheaf.Paper.ECoefficientSmoothBaseChange` | A6 | Two proofs completed; proved private comparison API added. |
| `Sheaf.Paper.QbarCoefficientSmoothBaseChange` | unclaimed | Existing signatures and definition bodies preserved; no adaptation. |

## Status

landed 20261021T100726-L-4121929 2026-10-21 (merge of deliver/A6/Sheaf.Paper.ECoefficientSmoothBaseChange)
