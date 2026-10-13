## What changed

Proved `sheaf_finiteType_of_epi` by extracting finite local-generators data for the source,
transporting each finite generating family along the restricted epimorphism, and reassembling
the same cover for the target. Added `Sheaf.AlgebraicGeometry.EpiOverFunctor` with the
restricted-epimorphism intermediate theorem. Removed the unused sheafification import from
the item module.

## Proved and sorry left

The target hole `sheaf_finiteType_of_epi` is closed. The new intermediate theorem
`epi_overFunctor_map` remains `sorry`, with node `lem-stage3-epi-over-functor`.

## No longer needed

Removed `WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification` from the
item module; no other planned dependency was used.

## Where the brief, the DAG or earlier work was wrong

The planned direct use of `GeneratingSections.ofEpi` omitted the necessary fact that restriction
to each over-site preserves epimorphisms. This is a genuine intermediate step, so it was split
off as `lem-stage3-epi-over-functor` rather than hidden in the proof.

## New nodes

`lem-stage3-epi-over-functor`: restricted over-site maps of epimorphisms are epimorphisms;
module `Sheaf.AlgebraicGeometry.EpiOverFunctor`; change record `coord/changes/epi-over-functor-import.md`.

## Earlier second reading (a previous round; superseded)

The proof has been independently checked by compiling both sandbox modules. The target
statement is unchanged. The added theorem is strictly the missing restriction-of-epi step and
is exactly what the local-generator construction requires; the unit route is retained.

## Second reading by B4

1. **Statements and interfaces.** Compared the delivered item declaration byte for byte with
   `lean/Sheaf/AlgebraicGeometry/FiniteTypeEpiImage.lean`; the target signature is unchanged.
   The new `epi_overFunctor_map` declaration is a strictly smaller intermediate statement and
   has the required blueprint node and source.
2. **Compilation and proof audit.** Compiled both delivered modules with `lcompile.py --all`.
   The target proof contains no `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, or
   `implemented_by`; the only remaining hole is the explicitly named `epi_overFunctor_map`.
3. **Truth and strength of split statement.** The split theorem states exactly that restriction
   along an over-site preserves an epimorphism, which is the local lifting fact used by the
   generator transport. Its hypotheses match the target's sheafification assumptions and it is
   not a restatement of the target.
4. **Route and pruning.** The proof keeps the unit route through local generators and
   `GeneratingSections.ofEpi`, while removing the unused sheafification import. The new private
   proof import is needed only to install the restricted epi instance.
5. **DAG and records.** Checked that the item and split node statements, proof steps,
   `proof_deps`, module/declaration fields, and the import change record agree with the Lean
   files. No target statement or definition was changed.

I additionally removed the unused `PushforwardContinuous` public import from the new intermediate
module; it compiles with only the Abelian and Generators imports. The linter suppression remains in
the item module because the proof's local instance bindings trigger the style warning.
