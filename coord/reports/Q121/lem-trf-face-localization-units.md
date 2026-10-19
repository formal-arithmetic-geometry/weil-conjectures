# Stage-1 report: lem-trf-face-localization-units

Files written:

- `dag/nodes/sec-trace-formula/lem-trf-face-localization-units.json`: item split into two elementary proof steps; no new nodes.
- `citations.json`: empty, because both proof steps use only the hypotheses and definitions displayed in the item.

Attachments: none. There is no sorry-free declaration in `WeilConjectures/` tagged `(blueprint: lem-trf-face-localization-units)` or otherwise stating this item exactly.

WANTED: none.

The existing `lem-trf-fs-face-sharpening` node contains the same units conclusion under the strictly stronger fine-saturated hypotheses. It is not a duplicate of this item and cannot be cited to prove the present integral-only statement. No statement or blueprint error was found.

## Not duplicates

`lem-trf-face-localization-units` vs `lem-trf-fs-face-sharpening`: the existing node assumes that Q is fine and saturated and concludes several additional quotient properties, whereas this item assumes only integrality and concludes only the units characterization.

## Review by Q121

I read the item and its source, Illusie–Laszlo–Orgogozo, Exposé VIII §§3.1.1–3.1.2 (printed pages 98–99), where sharpening, localization, and the face-localization convention are given. I also read the imported related nodes `lem-trf-face-localization-fs`, `lem-trf-face-subgroup-saturated`, and `lem-trf-fs-face-sharpening` to check for an existing statement that could be cited; none has the present hypotheses and conclusion. The first proof step checks the inclusion (F^{\rm gp}\subseteq Q_F^\times): each (f\in F) is represented by (f-0), with inverse (0-f), and units are closed under products and inverses. The second checks the reverse inclusion: writing a unit and its inverse as (q-f) and (q'-f'), their sum gives (q+q'=f+f') in (Q^{\rm gp}); the stated injectivity of (Q\to Q^{\rm gp}) moves this equality back to Q, and the face condition forces (q,q'\in F), so the unit is in (F^{\rm gp}). Both steps are elementary and cite no external node, so `citations.json` is empty. I tested the statement on (Q=\mathbf N) with (F=\{0\}), (F=Q), and (Q=\mathbf N^2) with a coordinate face; the units are respectively (\{0\}), all of (Q^{\rm gp}), and the expected coordinate subgroup. The Mathlib search log includes LeanFinder, Loogle, grep, and LeanSearch queries in two phrasings; all returned only general localization declarations and no exact result.

What could not be finished: nothing.
