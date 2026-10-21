## What changed

Proved `AlgebraicGeometry.Etale.finiteRing_constant_derived_mapping_sheaves` with its original statement. Added two proved supporting modules: `Sheaf.CategoryTheory.BoundedConstantModuleChainMapLocal` descends bounded finite-source chain maps, and `Sheaf.AlgebraicGeometry.FiniteRingConstantDerivedMapLocal` constructs local algebraic representatives of derived maps.

The derived-map proof uses the existing Noetherian pseudo-coherence criterion and arbitrary-degree finite-free approximation. Orthogonality and the exact sequences of a triangle and its inverse rotation compare maps from the approximation, both algebraically and after exact constant realization and inverse image. Local-actual supplies chain representatives. The new chain-map lemma descends their finitely many components, using constant-section injectivity to check the chain equations. Covering sieves are assembled using the joint-surjectivity characterization of the small etale topology.

An exact geometric stalk retracts constant realization on every nonempty scheme. This proves local uniqueness directly. For Isom, lift the map and its inverse and use local uniqueness to make the two algebraic composites identities. Locally bijective maps become isomorphisms after sheafification. No existing statement, definition or public import changed.

## Proved and sorry left

Closed one original hole: `AlgebraicGeometry.Etale.finiteRing_constant_derived_mapping_sheaves`.

Added zero holes. Both `CategoryTheory.exists_bounded_constant_module_chain_map_local` and `AlgebraicGeometry.Etale.finiteRing_constant_derived_map_local` have complete proofs. No `sorry` remains in the packet. No unfinished result is split off.

The new statements include the zero ring, zero complexes, empty support intervals, and objects covered by the empty sieve. The main proof handles the empty scheme through its bottom covering sieve and permits an empty algebraic Isom set.

## No longer needed

The specialized finite-module exactness theorem `lem-constructible-constant-exact` is unnecessary: the general constant-sheaf functor has proved finite-limit and finite-colimit preservation instances.

The direct finite-cone resolution construction and `lem-pc-ring-derived-map-representative` are unnecessary: the existing pseudo-coherence APIs give the required bounded approximation. `lem-pc-ring-finite-cone-free-model` remains a transitive dependency of that API and is not withdrawn.

The local-nullhomotopy half of `lem-weil-pbc-finite-free-etale-local-actual` and `lem-weil-pbc-site-sheafification-sections-local` are unnecessary. Exact stalk faithfulness proves local injectivity, and the locally-bijective sheafification API supplies the sheaf comparison. The local-actual module remains needed for its chain-representative half.

Removed direct proof imports from the item: `WeilConjectures.AlgebraicGeometry.ConstantEtaleSheafShortExact`, `WeilConjectures.RingTheory.FiniteConeFreeModel`, `WeilConjectures.AlgebraicGeometry.SiteSheafificationSectionsLocal`, `WeilConjectures.AlgebraicGeometry.ConstantSheafGeometricStalk`, `Mathlib.Algebra.Homology.DerivedCategory.KProjective`, `Mathlib.Algebra.Homology.DerivedCategory.TStructure`, `Mathlib.CategoryTheory.Triangulated.Pretriangulated`, and `Mathlib.Algebra.Homology.ShortComplex.ShortExact`. The proof import of `Sheaf.Paper.FiniteFreeEtaleLocalActual` moves to the local-representative module. No existing module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

No statement error was found. The planned homotopy descent is longer than necessary: a geometric module stalk is an exact retraction of constant realization, which already gives derived faithfulness on nonempty schemes. Inverse pairs reduce Isom surjectivity to Hom surjectivity and local uniqueness. Updated the item node to reflect this route.

The bounded finite-free approximation uses two already proved tools: `lem-weil-pbc-noetherian-pseudocoherent-cohomology-criterion` and `lem-pc-ring-pseudo-coherent-iff-all-m`. These replace the direct finite-cone construction while retaining the approximation and orthogonality steps of the planned argument.

## New nodes

`lem-weil-pbc-bounded-constant-module-chain-map-local` records the proved fixed-ring module-sheaf chain-map descent result. The existing ringed-module version has a different coefficient category; the new result uses constant-module morphism descent directly and avoids building an equivalence of ringed module realizations and their slice restrictions.

`lem-weil-pbc-finite-ring-constant-derived-map-local` records the proved local existence step for derived maps of bounded finite constant complexes. It contains the approximation, triangle comparison and local chain-representative argument. It is a strict part of the main theorem, with no local uniqueness or sheafification comparison in its conclusion.

Change record: `coord/changes/finite-ring-constant-derived-mapping-proof-commands.md`. The static scanner classifies added elaboration and namespace commands as an interface change; the record confirms that public signatures, definitions, imports and instances remain unchanged.

## Second reading by B2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
