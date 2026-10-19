## Worker report

The item is already stated by the landed module `Sheaf.TraceFormula.FinitarySiteCoherentGenerators`, declaration `CategoryTheory.finitarySiteCoherentGenerators`. I inspected the module and its complete theorem signature. It states the node clause by clause: `C` is a category with explicit universes and finite limits; `J` is a site precoverage; every covering presieve is finite; the sheaf topos is `Sheaf J.toGrothendieck (Type (max u v w))`; every sheafified ulifted representable is coherent; these representables generate by an epimorphic `Sigma.desc`; there is an object property containing the generators, consisting of coherent objects and closed under all finite-limit shapes; and every geometric morphism from a coherent target whose inverse image preserves each generator is coherent. The proof is intentionally `sorry`, as required for stage 2.

The exact dependency declarations used by the module are:

- `CategoryTheory.Precoverage.IsSiteForCoverings` from `Sheaf.CategoryTheory.SiteCoveringAxioms` for the site hypothesis.
- `CategoryTheory.presheafToSheaf` from `Mathlib.CategoryTheory.Sites.Sheafification` for sheafification.
- `CategoryTheory.IsCoherentTopos`, `IsCoherentObject`, and `IsCoherentGeometricMorphism` from `Sheaf.CategoryTheory.Sites.CoherentTopos`.
- `CategoryTheory.GeometricMorphism` from `Sheaf.CategoryTheory.Sites.GeometricMorphism`.

The size-convention dependency is a metatheoretic convention and has no Lean declaration. The module binds all universes explicitly (`u v u' v' w`) and uses `max u v w`, so it does not exclude empty index types or any finite-cover edge case. I checked the empty coproduct/empty family cases in the statement's `Type (max u v w)` quantification and the identity/trivial-site cases of the site hypothesis.

I searched for duplicates with `msearch.py` (LeanFinder query for finite-cover coherent sheaf topoi, Loogle queries for coherent sheaf/topos declarations, and grep over Mathlib, `WeilConjectures`, `lean/Sheaf`, and `dag/nodes`). Mathlib's coherent-topology declarations concern sheaf conditions and do not state this coherent-object criterion; the source checkout has no declaration of this theorem. The exact declaration is already present in the shared `newtargets-dag` Lean tree, so this delivery reuses it rather than introducing a second definition.

The node copy changes only its `lean` record attribution to this Q28 delivery; all statement, dependencies, proof, and metadata fields are preserved verbatim.

## Second reading by Q28

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
