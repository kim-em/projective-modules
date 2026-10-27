# Historical API records

[API display archive](API.md) and [original manifest](api-manifest.json) retain the
selected native displays and producer metadata inherited from release
`52241359db5999182a2ae97e291a9ba1e4194df4`. The manifest describes source
`5d1b1b276d4a11ee6ce9ae238c9511de8dbec1e9`, Lean 4.34.0-rc2 and the older
dependency graph. The inherited display already contained source amendments, including componentwise-free
notes, renamed PID helper displays, added docstrings and generalized split-kernel signatures.
Not every amendment had a native run or an individual marker. The adapter tests explicitly
use synthetic overrides for the three split-kernel signatures rather than relabel the
original inventory.
The archived links have been qualified with the recorded source revision.
No fresh native generation or proof certification is claimed.

`scripts/api_inventory.json` and `scripts/generate_api.py` remain a historical,
fixed-inventory adapter. They do not enumerate the current library. Reproduction
requires the original source, native declaration records and SQLite database;
these are not shipped, and the original source revision is unavailable from the
public origin. The Python suite tests its parser and refusal controls using
synthetic records and synthetic line fixtures. Passing it is not native evidence.

Use the [current API guide](../API.md) for the migrated library.
