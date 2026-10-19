## Worker report

The module `lean/Sheaf/CategoryTheory/Sites/CoherentTopos.lean` states the six notions in the node. `CategoryTheory.IsQuasiCompactObject` renders the hypothesis that an epimorphic coproduct `Sigma.desc f` onto `A` has a finite subfamily `s : Finset I` whose coproduct is epi. `CategoryTheory.IsQuasiSeparatedObject` quantifies maps `B ⟶ A` and `C ⟶ A`, assumes both `IsQuasiCompactObject`, and says every pullback square `IsPullback p q f g` has quasi-compact vertex. `CategoryTheory.IsCoherentObject` is the conjunction of these two predicates.

`CategoryTheory.IsCoherentTopos` assumes coproducts and finite limits, requires `IsGrothendieckTopos.{w} E`, gives a small type `G` of coherent generators, requires each `obj i` coherent, requires every object to receive an epimorphism from a coproduct indexed by a small type of generators, and requires the property `P X := ∃ i, Nonempty (X ≅ obj i)` to satisfy `ObjectProperty.IsClosedUnderLimitsOfShape P J` for every finite category shape `J` (including the empty shape, hence the terminal object). `CategoryTheory.IsCoherentGeometricMorphism` takes coherent-topos hypotheses and states that the inverse-image functor sends every coherent object to a coherent object. `CategoryTheory.IsConservativeGeometricMorphism` states that if the inverse image maps a morphism to an isomorphism then the original morphism is an isomorphism.

The recorded `def-weil-pbc-topos` declaration `CategoryTheory.IsGrothendieckTopos` already exposes the size universe as its explicit universe parameter, so the module uses `IsGrothendieckTopos.{w} E`; no dependency repair module is included. The other dependencies are used through `Sheaf.CategoryTheory.Sites.GeometricMorphism` (`CategoryTheory.GeometricMorphism`) and the size convention node (which is metatheoretic and has no Lean declaration).

Edge cases checked: the quantifier `I : Type w` permits the empty family; `Finset I` permits the empty finite subfamily when its coproduct is epi; the pullback clause is stated for every chosen pullback square; the coherent generator type may be empty only when the generating-epi condition permits it; the empty finite shape in `IsClosedUnderLimitsOfShape` supplies terminal-object closure, while all finite shapes give finite-limit closure. No `sorry` occurs because this is a definition node.

Searches: `msearch.py grep coherent.?topos|coherent.?object|IsQuasiCompactObject|IsCoherent` found only unrelated Mathlib coherent-site files; `msearch.py loogle "Coherent", "Sheaf"` found only quasicoherent-module declarations; `msearch.py leanfinder` for coherent objects/topoi found no matching predicate; `rg` over `lean/Sheaf` and `WeilConjectures` found no coherent-topos or coherent-object declaration. The Mathlib hits `CategoryTheory.coherentTopology` concern coherent topologies, not coherent Grothendieck topoi. The existing `CategoryTheory.IsGrothendieckTopos` declaration was read and matches the required explicit universe parameter.

## Second reading by Q49

I independently reread the item, its statement dependencies, and `Sheaf.CategoryTheory.Sites.CoherentTopos`. The quasi-compact, quasi-separated, and coherent predicates match their clauses; the coherent-topos conjunction uses `IsGrothendieckTopos.{w} E`, a small generator type with coherent objects and epimorphic coproduct presentations, and explicit closure of the generator property under every `FinCategory` shape. The empty shape covers the terminal object. The two geometric-morphism predicates use exactly the recorded inverse-image functor and the stated preservation/reflection conditions. I found no remaining mismatch or duplicate declaration, and no dependency module is included.

## Maintainer review fix (2026-10-18)

The second reader of the maintainer made two changes. Both leave the meaning of the module unchanged.
`CategoryTheory.IsConservativeGeometricMorphism` now has the body `u.inverse.ReflectsIsomorphisms`
(Mathlib's `Functor.ReflectsIsomorphisms`). The delivered body wrote out the same condition,
`∀ f, IsIso (u.inverse.map f) → IsIso f`, by hand, which gave a second definition of the notion (H4).
The imports `Mathlib.CategoryTheory.Limits.Shapes.Multiequalizer` and
`Mathlib.CategoryTheory.ObjectProperty.FullSubcategory` were removed because nothing used them (H9).
The fixed file compiles clean with nt_compile.py.
