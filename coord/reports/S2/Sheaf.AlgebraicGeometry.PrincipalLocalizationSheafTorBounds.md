## What changed

Replaced the sorry in `AlgebraicGeometry.principal_localization_sheaf_tor_bounds`
with assembly of exact open restriction, degreewise tensor vanishing, and the
concrete termwise localization comparison. Its signature and docstring remain
byte for byte unchanged. Added two modules, one theorem per module:
`Sheaf.AlgebraicGeometry.OpenImmersionTensorVanishing` (proved during second reading)
and `Sheaf.AlgebraicGeometry.PrincipalLocalizationRestrictionModel` (still open).
The upper proof composes the K-flat witness's representing isomorphisms.

The second reader proved the degreewise restriction theorem from the existing
`isKFlat_restrict`, strong monoidal module pullback, restriction adjunction counit,
and Mathlib exact-functor homology and derived-category comparisons. The tensor
comparison is totalized termwise, including both differentials, using the already
proved calculation in `AffineSheafificationTensorVanishingTest.lean` as a guide.
The remaining localization model imports its recorded proof dependencies.
All newly added proof dependencies are plain imports; public imports supply signatures.

## Proved and sorry left

Closed original hole: `AlgebraicGeometry.principal_localization_sheaf_tor_bounds`
(node `lem-sc-principal-localization-sheaf-tor-bounds`).

New theorem proved: `AlgebraicGeometry.openImmersion_tensor_vanishing`
(node `lem-sc-open-immersion-tensor-vanishing`). The first worker left this sorry;
the second reader closed it without adding any further holes.

Added and left sorry: `AlgebraicGeometry.principalLocalization_restriction_model`
(node `lem-sc-principal-localization-restriction-model`).

This remains a decomposition with one original hole closed and one lower hole
added, net zero textual holes across the delivered modules. It is not a complete
proof of the original item: its dependency on the localization model remains open.
The final import-closure net and pruning are for the pinned sorry ledger to compute.
No definitions, existing signatures or visibility were changed. Existential functor
and morphism witnesses are unpacked only inside theorem proofs, never used to define
an arbitrary object.

## No longer needed

Removed the proof-only import `Sheaf.AlgebraicGeometry.AffineDerivedPullbackTensorTilde`.
Its node `lem-pc-affine-derived-pullback-tensor-tilde` is the sole old proof dependency
and is no longer directly used. The localization step uses exact termwise restriction
and tilde base change rather than derived monoidal infrastructure. This is a direct
import pruning; no assertion is made that this module is globally unreachable.
No unit statement or realized step was bypassed.

## Where the brief, the DAG or earlier work was wrong

The original plan's affine derived-pullback declaration concerns K-flat resolution
models with a shared localization universe, whereas this target needs concrete exact
localization of arbitrary complexes and independent universes. The model comparison
is now a separate strictly lower statement. The degreewise open-immersion theorem
has no localization data, interval, or affine hypotheses.

The first worker recorded proof dependencies of the localization model without
importing their modules. The second reader added the missing proof imports and
changed the degreewise theorem's DAG route to match its actual proved calculation.

Stacks Tag 09U8 proves interval preservation using bounded flat representatives;
the direct-image testing argument here is an agent-written degreewise specialization,
not the printed proof of that tag. Tag 08DW(2) gives affine derived base change;
exact localization specializes it to arbitrary termwise localized complexes.
The final statements include empty schemes, zero rings, f=0, invertible f,
zero and unbounded complexes, independently chosen derived-category universes,
and reversed intervals. No ordering assumption on a,b is introduced.

## New nodes

`lem-sc-open-immersion-tensor-vanishing`: proved preservation of all-module derived
tensor vanishing in one degree along an open immersion. Its proof dependency route
now records K-flat open restriction, existing strong monoidal scheme pullback, and
the restriction adjunction. No localization data or Tor interval occurs.

`lem-sc-principal-localization-restriction-model`: exact open restriction of the
associated-sheaf complex agrees with concrete termwise principal localization.
It has no Tor-amplitude hypothesis or vanishing conclusion. The docstring explains
factorization through D(f), uniqueness of left adjoints comparing tensor pullback
and restriction, the module localization universal property including Shrink,
and descent of natural complex isomorphisms through Q. No change records or forced
adaptations are needed.

## Second reading by S2

1. Compared the existing module with its repository version using diff and checked
   the complete declaration signature as literal text: unchanged. Only its proof
   and proof-only imports changed. Both other modules and their nodes are new.
   No definitions or declarations belonging to other items changed. Verdict: pass.
2. Read all proof terms. The upper proof transports the same K-flat representative;
   the restriction proof tests the direct image, constructs the tensor complex
   isomorphism, preserves homology, and uses the counit. There is one named theorem
   with sorry, matching the report and node; no hollow definition or forbidden
   declaration is present. All three files compiled in import order without
   warnings (18.9, 17.1 and 17.0 seconds). Scratch #print axioms checks show only
   propext, Classical.choice and Quot.sound for the restriction theorem; the model
   and upper theorem additionally have sorryAx, exactly as expected. Verdict: pass.
3. Checked both intermediate statements against the vanishing definition and the
   cited mathematics. Tested the empty source, f=0, unit f, zero ring, zero complex,
   unbounded complex, arbitrary degree and reversed interval: no counterexample.
   The statements are proper independent parts of the original argument. Searched
   with alternate leanfinder and loogle queries and Mathlib grep, and read the
   upstream and Sheaf restriction, K-flatness, tensor and affine-test declarations.
   Found ingredients and a reusable proved calculation, but no exact full model
   comparison or general public vanishing theorem. Verdict: pass.
4. Used the shorter existing strong monoidal pullback and K-flat restriction route
   to close the degreewise hole. Signature imports are public; proof imports are
   private to the module. The only original proof dependency is fully reported
   under No longer needed. Read `dag/units/sk-thm-picard-duality.json`: its realized
   statement and step lists are empty, and this work preserves the original two
   lower steps without changing the unit or chapter route. Verdict: pass.
5. Read each node and compared its Lean statement, module, declaration and proof
   route. The original node now records precisely the two assembly inputs; the
   restriction node records the actual proved calculation; the remaining model
   node records its intended restriction and tilde comparison inputs. New nodes
   have source, complete proof plan, searches, provenance, unit, chapter, blueprint
   and Lean records. Verdict: pass.

Second reading changed: proved `openImmersion_tensor_vanishing`, repaired the
localization model's missing proof-dependency imports, expanded its comparison
explanation, updated the restriction node's actual proof route, corrected progress
accounting and distinguished the degreewise argument from the printed 09U8 proof.
