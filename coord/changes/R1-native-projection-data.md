# Native proper projection record factorization

The item module Sheaf.Paper.NativeProperProjectionRealization keeps its theorem name
and exact signature. Its record NativeProperProjectionRealization now extends the
new NativeProperProjectionModels record, containing exactly the original resolution
fields up to and including pullTensor. The four projection fields are unchanged.
Every original mathematical data field and normalization equation remains present;
no object, property or hypothesis is removed or weakened. No definition chooses data
from an unproved theorem: both structures are ordinary data records, and existence
is eliminated only inside the final theorem proof.

The resolution fields remain available by inherited dot notation. Their previous
qualified flat projection constants are replaced by the model record projections;
there is no existing consumer of those constants in the snapshot. Lean reserves the
inherited field names, so defining compatibility constants at those names is rejected.

The constructor takes the resolution prefix as one parent record instead of a flat
list of arguments. The model module is therefore publicly imported by the original
module. The item node adds the model node as a statement dependency; the original
record and theorem remain attached to the item node. No other existing node changes.

The factorization is needed for the 60-second per-file limit. Profiling the flat
record and construction proof found substantial dependent field elaboration, kernel
type checking and linting. Local irreducibility of concrete cochain and localization
comparison maps did not reduce the cost enough. Factoring the shared data avoids
checking those large dependent field types twice.

No existing module in the shared snapshot imports the item (checked by rg over lean).
There are no forced adaptations. All original public imports remain; no adopted
WeilConjectures source file or other existing module is changed.
