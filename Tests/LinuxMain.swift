import XCTest
@testable import officialTests
@testable import expressionsTests

XCTMain([
    testCase(officialTests.allTests),
    testCase(expressionsTests.allTests),
])
