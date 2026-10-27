## What changed

Proved `AlgebraicGeometry.exists_source_fibre_differential_formula` in
`Sheaf.AlgebraicGeometry.SourceFibreDifferentialSectionsAux`, preserving its statement and
all existing public imports. Added a private proof import of
`WeilConjectures.AlgebraicGeometry.Modules.FlatPullbackStalk` for the existing linear stalk API.
The existing injectivity proof is preserved.

The construction uses the universal derivation to map source differentials into the
pushforward of the differential sheaf of the base-changed projection, then applies the
section-normalized tensor-pullback unit along g. Since the source projection of g factors
through the residue-field point, every neighbourhood of that point pulls back to all of T.
Compatible maps on neighbourhood sections therefore descend through the stalk colimit.
The scalar calculation uses the actual residue map and h_alpha. Restriction of relative
differentials and two applications of the tensor-Hom adjunction give D. Naturality and
the normalized unit give the exact formula, including the arbitrary restriction proof hV.
All four private auxiliary theorems are proved.

Updated the formula node's proof, proof dependencies and proof origin to describe this route.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.exists_source_fibre_differential_formula`
(node `lem-zl-source-fibre-differential-formula`).

Added zero holes. There are zero `sorry`s left in the delivered module.
The complete module compiled through lcompile.py in 27.8 seconds. Both public theorem
signatures and the existing injectivity proof and its helpers are preserved verbatim.
This is a proof, not a decomposition. The already-proved
`AlgebraicGeometry.source_fibre_differential_injective_of_formula` still depends on the
existing, separately assigned `AlgebraicGeometry.exists_source_fibre_differential_functional`
in `Sheaf.AlgebraicGeometry.SourceFibreDifferentialFunctionals`; that module is unchanged.

The construction allows empty T, a zero ring of global sections and a zero cotangent fibre.
It uses no finite basis or finite-dimensionality assumption. Smoothness is retained in the
public signature although this construction does not require it.

## No longer needed

No existing Lean import was removed. The existing proof imports remain necessary for
injectivity and its private helpers.

The formula proof does not use these former planned dependencies, removed from its
proof_deps and proof-step uses:

- `lem-trf-relative-differential-sheaf-base-change`, module
  `Sheaf.AlgebraicGeometry.RelativeDifferentialSheafBaseChange`: only the forward canonical
  differential morphism is needed, constructed directly from the universal derivation;
  no base-change isomorphism is needed.
- `lem-weil-pbc-module-stalk-pullback`, module
  `WeilConjectures.AlgebraicGeometry.Modules.TensorPullbackStalk`: the compatible maps to
  global sections descend directly through the source stalk colimit; no pullback-stalk
  isomorphism is needed.
- `lem-ag-smooth-relative-differentials-finite-locally-free`, module
  `WeilConjectures.AlgebraicGeometry.SmoothRelativeDifferentialsFiniteLocallyFree`: two
  tensor-Hom adjunctions construct the comparison without choosing a finite basis.

These dependencies may still be used elsewhere. No source-library declaration or module
is removed, and no unit statement or realized step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The previous plan used stronger machinery than existence of the forward comparison
requires. The universal derivation and the stalk colimit give the required map without
smooth finite local freeness, a differential base-change isomorphism, or a pullback-stalk
isomorphism. There is no statement correction.

Searches: Lean Finder for a cotangent-fibre/global-sections comparison returned generic
ring tensor and pullback-triplet results, with no direct comparison. Loogle did not know
`TopCat.Presheaf.stalkDesc`; the grep search returned unrelated scheme stalk maps. Local
search found the existing universal derivation, open-restriction differential morphism,
section-normalized adjunction and linear stalk API used in the proof.

The source read is Stacks Project, morphisms.tex, lemma-functoriality-differentials and
lemma-base-change-differentials, together with sheaves.tex, the module stalk colimit and
pullback construction. The Lean proof writes out the colimit and normalization argument.

## Second reading by B4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
