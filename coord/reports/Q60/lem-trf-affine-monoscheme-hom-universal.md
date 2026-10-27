## Worker report

This is a stage-2 statement delivery, preserving the accepted stage-1 split and every node field except `lean`. The inherited BLOCKED ending confused Q159's stage-1 PASS (2026-10-23) with completion of stage 2: the current item has no `lean`, no `reviewed_lean`, and no released repair note. The stage-handoff rule in coord/brief-stage2.md §0 explicitly permits its stage-2 formalization. No stage-1 proof step is reopened.

Module: `Sheaf.AlgebraicGeometry.AffineMonoschemeHomUniversal`. Main declaration: `AlgebraicGeometry.Monoscheme.affine_hom_universal`. Helper: `AlgebraicGeometry.Monoscheme.affinePullback`, a real composite of the dependency's canonical numerator map and Mathlib's global-sections map. The only postponed proof is the main theorem; its docstring reproduces all seven accepted proof steps and their dependencies.

Read source: ILO, Exposé VIII, 3.1.2--3.1.8, printed pp.98--99, particularly 3.1.8(i), from the repository PDF via pdftotext. The theorem is the unsharpened assertion (i); assertion (ii) imposes sharp stalks and uses the sharp spectrum, and is deliberately a different existing node. The current blueprint location is a supporting input to the local-term-locality branch rather than a unit's own statement.

Hypothesis and clause correspondence:

- A fine commutative monoid P: `(P : Type u) [CommMonoid P] (hP : FineFan.IsFine P)`. Multiplicative notation encodes the source's additive notation; `1` denotes its `0`. Fineness is exactly finite generation and injectivity into the group completion, with no sharpness or torsion-free assumption.
- Its unsharpened spectrum A(P): `Monoscheme.affine P`, not `FineFan.affine P`. It uses the dependency's monoid prime topology and actual unsharpened localization sheaf.
- Any space T with a sheaf A of commutative monoids: `T : SheafedSpace CommMonCat.{u}`. This bundles precisely the topological space and sheaf, with no affine, finiteness, integrality, sharpness or nonemptiness restriction. The universe is arbitrary; simultaneous placement in a common universe entails no mathematical size restriction.
- A continuous map with restriction-compatible section homomorphisms: the Mathlib morphism `T ⟶ affine P`. Its underlying morphism carries `hom.base` and the sheaf natural transformation `hom.c`.
- Locality of every stalk homomorphism: `{f : T ⟶ affine P // FineFan.IsLocalMorphism f}`. The dependency defines this by `IsLocalHom` on its actual filtered-colimit stalk maps, meaning inverse image of units is units.
- Pullback of canonical global sections: `affinePullback f.val`, defined by `(SheafedSpace.Γ.map f.op).hom.comp (affineSection P)`. The canonical numerator map is the prescribed identification from P, so no arbitrary global-section isomorphism is introduced.
- The asserted bijection: first conjunct `∀ T, Function.Bijective (...)`; the codomain is exactly `P →* T.presheaf.obj (op ⊤)`. Bijectivity of the prescribed function is the stated natural bijection and fixes its forward map.
- Naturality in the monoidal source: second conjunct, for arbitrary T, T', local k and local f, `affinePullback (k.val ≫ f.val) = (SheafedSpace.Γ.map k.val.op).hom.comp (affinePullback f.val)`.
- Naturality in P under monoid homomorphisms: third conjunct, for any fine Q and any `v : P →* Q`, there is a unique local spectrum morphism g with `affinePullback g.val = (affineSection Q).comp v`. For every local `f : T ⟶ affine Q`, its additional equation is `affinePullback (f.val ≫ g.val) = (affinePullback f.val).comp v`. Existence and uniqueness are part of the same canonical correspondence applied to affine Q, and this characterization gives identity/composition of spectrum maps. There is no restriction that v itself be local.

Dependency declarations read and used:

- `Sheaf.AlgebraicGeometry.FineFanBlowup`: full signatures/docstrings of `AlgebraicGeometry.FineFan.IsFine`, `MonoidPrime`, `spectrumTopology`, `spectrumSections`, `spectrumRestriction`, `spectrumPresheaf`, `spectrumSheaf`, `stalkDiagram`, `stalk`, `germ`, `stalkMap`, and `IsLocalMorphism`.
- `Sheaf.AlgebraicGeometry.MonoschemeToricRealization`: full signatures/docstrings of `AlgebraicGeometry.Monoscheme.affine`, `affineSection`, `affineGerm`, `IsAffineMap`, `Fine` and `Hom`. We use the general sheafed-space subtype rather than the `Fine` source, which would incorrectly impose a finite affine cover.
- `Mathlib.Geometry.RingedSpace.SheafedSpace`: `AlgebraicGeometry.SheafedSpace.Γ`, including `Γ_obj_op` and `Γ_map_op` identifying its object and section pullback.
- Proof dependency `lem-weil-pbc-sheaf-morphism-on-basis` is a Mathlib leaf. Read `TopCat.Sheaf.restrictHomEquivHom`, `extend_hom_app`, `hom_ext`, and `isIso_iff_isIso_basis` in `Mathlib.Topology.Sheaves.SheafCondition.Sites`; import this as a proof-only import.
- Proof dependency `lem-trf-monoid-prime-minimal-neighborhood` currently has no Lean record or Mathlib match, so there is no module to import yet. Its mathematical use remains in the proof docstring, and its accepted DAG proof dependency is unchanged.

Edge cases checked before writing: T empty (both sets singleton); P the trivial monoid (terminal affine monoidal space); P a nontrivial finitely generated group (one spectrum point, retaining all units); P the additive natural numbers, with a chosen section whose germ can be a unit or nonunit; nonintegral/nonsharp target stalks; empty basic inverse images; nonlocal v between fine monoids, whose induced spectrum map is nevertheless locally monoidal. No positive-rank, characteristic, cancellation or sharpness hypothesis was added. Locality is substantive: for example, the inclusion of the additive natural numbers into the additive integers fails to reflect units and is excluded as a stalk map. No statement fault or STATEMENT-DISPUTED flag.

Searches actually run through `msearch.py Q60 lem-trf-affine-monoscheme-hom-universal` (saved by the wrapper in searches.jsonl):

- LeanFinder query: `Local morphisms from an arbitrary sheaf of commutative monoids on a topological space to an unsharpened fine monoid spectrum correspond naturally to homomorphisms into global sections.` Result: eight hits. Seven are ringed-space/GammaSpec constructions requiring commutative rings; the remaining `CategoryTheory.Sheaf.ΓHomEquiv` identifies constant-presheaf maps with global sections, with no monoid spectrum. Read the GammaSpec signatures and global-sections equivalence. No exact match.
- Loogle query: `"MonoidSpectrum", "MonoidalSpace"`. Result: service answered, zero hits.
- Mathlib grep query: `MonoidSpectrum|MonoidalSpace|monoscheme|affine_hom_universal`. Result: zero hits.
- Direct rg of `lean/WeilConjectures` and `lean/Sheaf` for the node id and monoid spectrum/universal-property names: no declaration for this node. `Sheaf.AlgebraicGeometry.AffineFanHomUniversal` supplies `AlgebraicGeometry.FineFan.affine_hom_universal`, read in full: it assumes sharp P and sharp source stalks and uses the sharpened sheaf, so it cannot state this item. Its `FineFan.affinePullback` is a different canonical map for that sharp target. The unsharpened `Monoscheme.affinePullback` is not already defined.
- DAG check: `lem-trf-monoid-spectrum-hom-universal` is a known duplicate assertion recorded by Q159's reviewer, but also has no Lean record, so provides no reusable declaration. No new node is needed.

Validation: the delivered file is checked using the prescribed server scompile.py wrapper. No global build, local Lean build, direct Git command or write to the shared repository was performed.

The first server compile rejected the new-module header because the published dependencies use the legacy module format. The delivered header now follows that dependency format; the mathematical signature was unchanged.

## Second reading by Q60

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
