## What changed

Completed the proof of `AlgebraicGeometry.Etale.restrictedAffineSingleTransition_composition_law`
in `Sheaf.AlgebraicGeometry.RestrictedAffineSingleCompositionLaw`. The theorem signature,
visibility and public import are unchanged. The second reader corrected the docstring
to identify the zero source used in nonzero degrees. Five private categorical helper
lemmas establish inverse-image square pasting, coefficient composition, and the generic
degree-zero single-complex calculation, after which the concrete restricted transitions
follow by specialization.

The DAG node proof and proof dependencies match the implemented route. No other module,
definition, or public statement was changed.

## Proved and sorry left

The sole original hole,
`AlgebraicGeometry.Etale.restrictedAffineSingleTransition_composition_law`
(blueprint `lem-sbc-restricted-affine-single-composition-law`), is proved. No `sorry`s
remain and no new holes were added.

## No longer needed

None. The existing public import and both proof-dependency nodes remain needed.

## Where the brief, the DAG or earlier work was wrong

No mathematical or interface error was found. The proof realizes the planned horizontal
pasting and single-complex comparison argument directly, with zero source components in
all nonzero degrees.

## New nodes

None.

## Second reading by P4

1. Compared the only delivered Lean module with the repository using `diff` and
   checked the existing theorem signature byte for byte. It is unchanged; all five
   new helpers are private proved lemmas. No definition or public interface changed.
2. Compiled the module locally with `lcompile.py`: no errors or warnings. Scanned
   for holes and forbidden declarations: none. The scratch-copy axiom check of
   `AlgebraicGeometry.Etale.restrictedAffineSingleTransition_composition_law` shows
   `[propext, Classical.choice, Quot.sound]`, with no `sorryAx`; the delivery probe
   also checks all helpers.
3. No statements were split off and no new holes or nodes were added. Read all five
   helpers: they establish associativity components, commuting-square pasting,
   coefficient composition, and the single-complex comparison. The argument covers
   empty index types vacuously and zero sheaves; the nonzero-degree calculation uses
   a zero source. No nonemptiness, directedness, affine hypothesis or identity law
   was silently introduced.
4. Read the imported concrete transitions and coefficient constructions and searched
   the library and Mathlib for single-comparison composition/naturality and inverse-image
   square pasting. Mathlib supplies the component and naturality lemmas used here;
   no existing complete restricted-composition theorem offers a shorter route.
   The sole public import is needed by the statement. Both original proof dependencies
   remain used, so `No longer needed: None` is complete. The unit record
   `dag/units/sk-lem-failure-field.json` is unchanged; this proof only supplies the
   original restriction-composition component below the unit level.
5. Compared the delivered node with the repository. Only `proof` and `proof_origin`
   differ. Its dependency set and Lean statement agree with the implementation:
   concrete restricted maps, inverse-image associativity and naturality, then the
   degree-zero calculation. There are no new nodes requiring additional metadata.

Changed only the theorem's proof docstring during this reading: it now says the
source single complex is zero in nonzero degrees, matching `isZero_single_obj_X`
and `eq_of_src` in `single_comp` and the already corrected DAG proof. The Lean proof
was retained. Closed one original hole and added zero holes; this is a proof, not a
decomposition.
