## Worker report

The module `Sheaf.Algebra.Homology.LeftResolutionReducedClass` states
`CategoryTheory.Abelian.leftResolution_reduced_class` with proof `sorry`, sourced from
`literature/blueprint/main-20261015/blueprint/sec-proetale-coefficients/sk-def-sfb-derived-tensor-hom/lem-sfb-derived-monoidal.proof.md`, first three sentences.
The module imports `Mathlib.Algebra.Homology.LeftResolution.Reduced`; the statement
uses Mathlib's `CategoryTheory.Abelian`, `ObjectProperty`, `IsZero`, biproducts,
`Epi`, functors, natural transformations, and preservation classes directly.

The hypotheses are rendered as follows.  `A : Type u` with `[Category.{v} A]` and
`[Abelian A]` is the abelian category hypothesis `[def-sp-abelian]`.  `F :
ObjectProperty A` is the class of objects.  `P : A ⥤ A` and `ε : P ⟶ 𝟭 A` are the
functorial cover and its natural transformation.  `hF_zero : ∃ Z : A, IsZero Z ∧ F Z`
says that a zero object belongs to the class.  `hF_iso : ∀ {X Y : A}, F X →
(X ≅ Y) → F Y` is closure under isomorphisms.  `hF_biproduct : ∀ (X Y : A), F X →
F Y → F (X ⊞ Y)` is closure under finite binary biproducts; together with the zero
object this gives closure under finite biproducts.  `hF_retract : ∀ {X Y : A}
(i : X ⟶ Y) (e : Y ⟶ X), i ≫ e = 𝟙 X → F Y → F X` is closure under retracts (the
object `X` is a direct summand of `Y`).  `hP : ∀ X : A, F (P.obj X)` says that `P`
has values in `F`.  `hε : ∀ X : A, Epi (ε.app X)` says that every component of `ε`
is epi.

The conclusion binds `C : Type u` and `cC : Category.{v} C`, preserving the full
subcategory universes, then `pC : @Preadditive C cC`, `zC : @HasZeroObject C cC`,
`fcC : @HasFiniteCoproducts C cC`, and `zmC : @HasZeroMorphisms C cC`.  The last
field is the zero-morphism structure induced by preadditivity and is made explicit
so the subsequent preservation predicate has all of its typeclass arguments.  The
functor `ι : C ⥤ A` is written with explicit category structures.  The conjunction
`@Functor.Full ... ι ∧ @Functor.Faithful ... ι ∧ @Functor.Additive ... ι` renders
fullness, faithfulness, and additivity.  `(∀ X : C, F (ι.obj X))` is the landing
condition.  The nested existential binds `Q : A ⥤ C`, `zQ :
@Functor.PreservesZeroMorphisms ... Q`, and `π : Q ⋙ ι ⟶ 𝟭 A`; its final clause
`∀ X : A, Epi (π.app X)` gives epimorphic components.

The proof docstring records both proof steps.  First, the full subcategory on `F`
inherits a zero object and finite coproducts, is full, faithful and additive, and is
idempotent complete by the abelian splitting theorem and retract closure.  Second,
`P` and `ε` form a left resolution of its inclusion and
`CategoryTheory.Abelian.LeftResolution.reduced` supplies the zero-morphism-preserving
`Q` and epi augmentation.

The statement dependencies are the recorded Mathlib matches: `def-sp-abelian`
uses `CategoryTheory.Abelian`; `lem-sfb-abelian-idempotent-complete` uses
`CategoryTheory.Idempotents.isIdempotentComplete_of_abelian`; and
`lem-sfb-left-resolution-reduced-api` uses
`CategoryTheory.Abelian.LeftResolution.reduced`, its
`PreservesZeroMorphisms` instance, and `LeftResolution.epi_π_app`.  No dependency
module was needed because all three declarations are Mathlib matches.

Edge cases checked before writing were: `F` equal to the class of only zero objects;
`F` equal to all objects; a zero input object of `P`; identity isomorphisms in the
isomorphism closure; the identity retract (`i = e = 𝟙`); empty finite coproducts
provided by `zC`; and the identity functor with identity epimorphism as a cover.
The finite-biproduct clause is binary plus the separately stated zero object, which
covers all finite biproducts by induction.

Searches for an existing declaration were made with:

- `msearch.py NK lem-sfb-left-resolution-reduced-class leanfinder "full subcategory of abelian category class closed under isomorphisms finite biproducts direct summands functorial epimorphic cover"`: generic object-property and idempotent-completion results only; no exact declaration.
- `msearch.py NK lem-sfb-left-resolution-reduced-class loogle "CategoryTheory.Abelian.LeftResolution.reduced, CategoryTheory.Abelian.LeftResolution, CategoryTheory.FullSubcategory"`: no hits (the qualified query is not accepted by Loogle).
- `msearch.py NK lem-sfb-left-resolution-reduced-class grep "LeftResolution.reduced|LeftResolution.karoubi|FullSubcategory" Mathlib/Algebra/Homology/LeftResolution`: no exact class-packaging declaration.
- `rg` over `WeilConjectures/` and `lean/Sheaf/` for `left-resolution-reduced-class`, `LeftResolution.reduced`, and the class-closure wording: no existing project declaration.
- `grep -rl 'lem-sfb-left-resolution-reduced-class' dag/nodes`: only this node and its reviewed citers; no existing Lean record for the item.

The required per-file compile was run with
`python3 /home/ubuntu/weil-launcher-nt/scompile.py NK lem-sfb-left-resolution-reduced-class lean/Sheaf/Algebra/Homology/LeftResolutionReducedClass.lean`.
It compiled successfully with no warnings other than the expected `sorry` notice.
No `STATEMENT-DISPUTED` flag or node fault was found.

## Second reading by NK

I reread the node, the full theorem signature, and the Mathlib declarations named by
its dependencies.  Every node hypothesis has a corresponding binder: abelian `A`,
zero, isomorphism, biproduct and retract closure of `F`, the `F`-valued functor `P`,
and componentwise epimorphic `ε`.  The conclusion binds `C` at exactly `Type u` and
`Category.{v}`, includes the zero object and finite coproduct structures, and states
fullness, faithfulness, additivity, landing in `F`, zero-morphism preservation of
`Q`, and epi components of `π`.  The explicit `zmC` witness is the structure already
implied by `pC : Preadditive C`; it only supplies the instance argument of the
preservation predicate and does not strengthen the mathematical conclusion.  The
signature compiled cleanly, and I found no mismatch with the node statement or its
source.
